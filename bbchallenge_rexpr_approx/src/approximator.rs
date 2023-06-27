// use indexmap::IndexSet;

use itertools::Itertools;

use crate::{
    expr::*,
    omega_num::{consts, OmegaNum},
};

pub type ApproxExprIdx = u16;
pub type ApproxExprStore = Vec<ApproxExpr>;

#[derive(Debug, Clone)]
pub enum ApproxExpr {
    Var(VarId),
    Const(OmegaNum),
    Arrow {
        arrows: usize,
        times: ApproxExprIdx,
        payload: ApproxExprIdx,
    },
    Lin {
        expr: LinExpr,
        idx: ApproxExprIdx,
    },
    Exp {
        base: u16,
        idx: ApproxExprIdx,
    },
    Add {
        idx1: ApproxExprIdx,
        idx2: ApproxExprIdx,
    },
    Mul {
        idx1: ApproxExprIdx,
        idx2: ApproxExprIdx,
    },
    Rec {
        repeat: ApproxExprIdx,
        rexpr: ApproxExprIdx,
        init: ApproxExprIdx,
    },
}
pub fn shallow_to_string(approx_expr: &ApproxExpr) -> String {
    match approx_expr {
        &ApproxExpr::Var(_) => format!("b"),
        ApproxExpr::Const(c) => format!("(({c}))"),
        &ApproxExpr::Arrow {
            arrows,
            times,
            payload,
        } => format!("(10{{{arrows}}})^#{times} #{payload}"),
        &ApproxExpr::Lin {
            expr: LinExpr { mul, add, div },
            idx,
        } => {
            format!("({mul}*#{idx}+{add})/{div}")
        }
        &ApproxExpr::Exp { base, idx } => format!("{base}^#{idx}"),
        &ApproxExpr::Add { idx1, idx2 } => format!("#{idx1}+#{idx2}"),
        &ApproxExpr::Mul { idx1, idx2 } => format!("#{idx1}*#{idx2}"),
        &ApproxExpr::Rec {
            repeat,
            rexpr,
            init,
        } => format!("<#{repeat},#{rexpr},#{init}>"),
    }
}
pub fn deep_to_string(exprs: &ApproxExprStore, idx: ApproxExprIdx) -> String {
    let mut s = format!("#{idx}");
    while let Some(start_index) = s.find("#") {
        let end_index = start_index + s[start_index..].find("}").unwrap();
        s.replace_range(
            start_index..=end_index,
            &shallow_to_string(
                &exprs
                    [ExprIdx::from_str_radix(&s[start_index + 2..end_index], 10).unwrap() as usize],
            ),
        )
    }
    s
}
pub fn substitute(exprs: &ApproxExprStore, approx_expr: &ApproxExpr, value: &OmegaNum) -> OmegaNum {
    match approx_expr {
        &ApproxExpr::Var(_) => value.clone(),
        ApproxExpr::Const(c) => c.clone(),
        &ApproxExpr::Arrow {
            arrows,
            times,
            payload,
        } => todo!(),
        &ApproxExpr::Lin {
            expr: LinExpr { mul, add, div },
            idx,
        } => {
            (substitute_index(exprs, idx, value) * OmegaNum::from(mul as f64)
                + OmegaNum::from(add as f64))
                / OmegaNum::from(div as f64)
        }
        &ApproxExpr::Exp { base, idx } => OmegaNum::pow(
            OmegaNum::from(base as f64),
            substitute_index(exprs, idx, value),
        ),
        &ApproxExpr::Add { idx1, idx2 } => {
            substitute_index(exprs, idx1, value) + substitute_index(exprs, idx2, value)
        }
        &ApproxExpr::Mul { idx1, idx2 } => {
            substitute_index(exprs, idx1, value) * substitute_index(exprs, idx2, value)
        }
        &ApproxExpr::Rec {
            repeat,
            rexpr,
            init,
        } => {
            let repeat = substitute_index(exprs, repeat, value);
            if !repeat.is_integer()
                || repeat.is_sign_negative()
                || repeat > OmegaNum::from(100000.0)
            {
                panic!("Invalid repeat count: {repeat}")
            }
            let mut result = substitute_index(exprs, init, value);
            for _ in 0..f64::from(repeat) as i64 {
                result = substitute_index(exprs, rexpr, &result);
            }
            result
        }
    }
}
pub fn substitute_index(
    exprs: &ApproxExprStore,
    index: ApproxExprIdx,
    value: &OmegaNum,
) -> OmegaNum {
    substitute(exprs, &exprs[index as usize], value)
}
pub type BoundedApproxExpr = (ApproxExprIdx, OmegaNum);

pub type ApproxExprInnerWithHole = Box<ApproxExprWithHole>;
pub enum ApproxExprWithHole {
    Hole(usize),
    NoHole(ApproxExprIdx),
    Var(VarId),
    Const(OmegaNum),
    Arrow {
        arrows: usize,
        times_pre: ApproxExprInnerWithHole,
        payload_pre: ApproxExprInnerWithHole,
    },
    Lin {
        expr: LinExpr,
        idx_pre: ApproxExprInnerWithHole,
    },
    Exp {
        base: u16,
        idx_pre: ApproxExprInnerWithHole,
    },
    Add {
        idx1_pre: ApproxExprInnerWithHole,
        idx2_pre: ApproxExprInnerWithHole,
    },
    Mul {
        idx1_pre: ApproxExprInnerWithHole,
        idx2_pre: ApproxExprInnerWithHole,
    },
    Rec {
        repeat_pre: ApproxExprInnerWithHole,
        rexpr_pre: ApproxExprInnerWithHole,
        init_pre: ApproxExprInnerWithHole,
    },
}
pub type BoundedApproxExprWithHole<const HOLE_N: usize> = (ApproxExprWithHole, [OmegaNum; HOLE_N]);

pub struct BoundedApproxResult<'a> {
    src: &'a Exprs,
    store: ApproxExprStore,
    dst: Vec<Option<Vec<BoundedApproxExpr>>>,
}
fn min_num(lhs: OmegaNum, rhs: OmegaNum) -> OmegaNum {
    if lhs < rhs {
        lhs
    } else {
        rhs
    }
}
fn max_num(lhs: OmegaNum, rhs: OmegaNum) -> OmegaNum {
    if lhs > rhs {
        lhs
    } else {
        rhs
    }
}
const MAX_SAFE_INTEGER_F64: f64 = 9007199254740991.0;
impl<'a> BoundedApproxResult<'a> {
    pub fn new(src: &'a Exprs) -> Self {
        BoundedApproxResult {
            src: src,
            store: Vec::new(),
            dst: vec![None; src.len()],
        }
    }
    fn store_expr(&mut self, approx_expr: ApproxExpr) -> ApproxExprIdx {
        self.store.push(approx_expr);
        (self.store.len() - 1) as ApproxExprIdx
    }
    fn store_num(&mut self, num: OmegaNum) -> ApproxExprIdx {
        self.store_expr(ApproxExpr::Const(num))
    }
    fn fill_store<const HOLE_N: usize>(
        &mut self,
        approx_expr_with_hole: ApproxExprWithHole,
        fill_idx: [ApproxExprIdx; HOLE_N],
    ) -> ApproxExprIdx {
        match approx_expr_with_hole {
            ApproxExprWithHole::Hole(i) => fill_idx[i],
            ApproxExprWithHole::NoHole(idx2) => idx2,
            ApproxExprWithHole::Var(i) => self.store_expr(ApproxExpr::Var(i)),
            ApproxExprWithHole::Const(c) => self.store_expr(ApproxExpr::Const(c)),
            ApproxExprWithHole::Arrow {
                arrows,
                times_pre,
                payload_pre,
            } => {
                let times = self.fill_store(*times_pre, fill_idx);
                let payload = self.fill_store(*payload_pre, fill_idx);
                self.store_expr(ApproxExpr::Arrow {
                    arrows,
                    times,
                    payload,
                })
            }
            ApproxExprWithHole::Lin { expr, idx_pre } => {
                let idx = self.fill_store(*idx_pre, fill_idx);
                self.store_expr(ApproxExpr::Lin { expr, idx })
            }
            ApproxExprWithHole::Exp { base, idx_pre } => {
                let idx = self.fill_store(*idx_pre, fill_idx);
                self.store_expr(ApproxExpr::Exp { base, idx })
            }
            ApproxExprWithHole::Add { idx1_pre, idx2_pre } => {
                let idx1 = self.fill_store(*idx1_pre, fill_idx);
                let idx2 = self.fill_store(*idx2_pre, fill_idx);
                self.store_expr(ApproxExpr::Add { idx1, idx2 })
            }
            ApproxExprWithHole::Mul { idx1_pre, idx2_pre } => {
                let idx1 = self.fill_store(*idx1_pre, fill_idx);
                let idx2 = self.fill_store(*idx2_pre, fill_idx);
                self.store_expr(ApproxExpr::Mul { idx1, idx2 })
            }
            ApproxExprWithHole::Rec {
                repeat_pre,
                rexpr_pre,
                init_pre,
            } => {
                let repeat = self.fill_store(*repeat_pre, fill_idx);
                let rexpr = self.fill_store(*rexpr_pre, fill_idx);
                let init = self.fill_store(*init_pre, fill_idx);
                self.store_expr(ApproxExpr::Rec {
                    repeat,
                    rexpr,
                    init,
                })
            }
        }
    }
    fn on_top<const HOLE_N: usize, const N: usize>(
        &mut self,
        hole_exprs: [BoundedApproxExprWithHole<HOLE_N>; N],
        approx_expr_idx: [ApproxExprIdx; HOLE_N],
        bound: &OmegaNum,
    ) -> Vec<BoundedApproxExpr> {
        hole_exprs
            .into_iter()
            .map(|(approx_expr_with_hold, shallow_bound)| {
                (
                    self.fill_store(approx_expr_with_hold, approx_expr_idx),
                    approx_expr_idx
                        .iter()
                        .enumerate()
                        .map(|(i, &approx_expr_idx)| {
                            self.inverse_upper_bound_index(approx_expr_idx, &shallow_bound[i])
                        })
                        .fold(bound.clone(), max_num),
                )
            })
            .collect()
    }
    fn calculate_bounded_approximations(&mut self, index: ExprIdx) {
        if self.dst[index as usize].is_none() {
            let r = match self.src.get_index(index as usize).unwrap() {
                &Expr::Var(i) => vec![(self.store_expr(ApproxExpr::Var(i)), consts::ZERO)],
                &Expr::Const(c) => vec![(self.store_num(OmegaNum::from(c as f64)), consts::ZERO)],
                &Expr::Lin {
                    expr: LinExpr { mul, add, div },
                    idx,
                } => self
                    .get_approximation(idx)
                    .iter()
                    .flat_map(|(approx_expr_idx, bound)| {
                        if let ApproxExpr::Const(c) = &self.store[*approx_expr_idx as usize] {
                            vec![(
                                self.store_num(
                                    (c.clone() * OmegaNum::from(mul as f64)
                                        + OmegaNum::from(add as f64))
                                        / OmegaNum::from(div as f64),
                                ),
                                bound.clone(),
                            )]
                        } else {
                            self.on_top(
                                [
                                    (
                                        ApproxExprWithHole::Hole(0),
                                        [OmegaNum::pow(
                                            OmegaNum::from(10.0),
                                            OmegaNum::from(
                                                MAX_SAFE_INTEGER_F64
                                                    * (mul as f64 / div as f64).log10().abs(),
                                            ),
                                        )],
                                    ),
                                    (
                                        ApproxExprWithHole::Mul {
                                            idx1_pre: Box::new(ApproxExprWithHole::Hole(0)),
                                            idx2_pre: Box::new(ApproxExprWithHole::Const(
                                                OmegaNum::from(mul as f64 / div as f64),
                                            )),
                                        },
                                        [OmegaNum::from(
                                            MAX_SAFE_INTEGER_F64 * (add as f64 / mul as f64),
                                        )],
                                    ),
                                    (
                                        ApproxExprWithHole::Lin {
                                            expr: LinExpr { mul, add, div },
                                            idx_pre: Box::new(ApproxExprWithHole::Hole(0)),
                                        },
                                        [consts::ZERO],
                                    ),
                                ],
                                [*approx_expr_idx],
                                bound,
                            )
                        }
                    })
                    .collect(),
                &Expr::Exp { base, idx } => self
                    .get_approximation(idx)
                    .iter()
                    .flat_map(|(approx_expr_idx, bound)| {
                        if let ApproxExpr::Const(c) = &self.store[*approx_expr_idx as usize] {
                            vec![(
                                self.store_num(OmegaNum::pow(
                                    OmegaNum::from(base as f64),
                                    c.clone(),
                                )),
                                bound.clone(),
                            )]
                        } else {
                            self.on_top(
                                [
                                    (
                                        ApproxExprWithHole::Hole(0),
                                        [consts::arrow_max_safe_integer(2)],
                                    ),
                                    (
                                        ApproxExprWithHole::Arrow {
                                            arrows: 1,
                                            times_pre: Box::new(ApproxExprWithHole::Const(
                                                consts::ONE,
                                            )),
                                            payload_pre: Box::new(ApproxExprWithHole::Hole(0)),
                                        },
                                        [OmegaNum::pow(
                                            OmegaNum::from(10.0),
                                            OmegaNum::from(
                                                MAX_SAFE_INTEGER_F64
                                                    * (base as f64).log10().log10().abs(),
                                            ),
                                        )],
                                    ),
                                    (
                                        ApproxExprWithHole::Exp {
                                            base,
                                            idx_pre: Box::new(ApproxExprWithHole::Hole(0)),
                                        },
                                        [consts::ZERO],
                                    ),
                                ],
                                [*approx_expr_idx],
                                bound,
                            )
                        }
                    })
                    .collect(),
                &Expr::Add { idx1, idx2 } => self
                    .get_approximation(idx1)
                    .iter()
                    .cartesian_product(self.get_approximation(idx2))
                    .flat_map(|((approx_expr_idx1, bound1), (approx_expr_idx2, bound2))| {
                        match (
                            &self.store[*approx_expr_idx1 as usize],
                            &self.store[approx_expr_idx2 as usize],
                        ) {
                            (ApproxExpr::Const(c1), ApproxExpr::Const(c2)) => vec![(
                                self.store_num(c1.clone() + c2.clone()),
                                max_num(bound1.clone(), bound2.clone()),
                            )],
                            (ApproxExpr::Const(c), e) => self.on_top(
                                [
                                    (
                                        ApproxExprWithHole::Hole(1),
                                        [consts::ZERO, c.clone() * consts::MAX_SAFE_INTEGER],
                                    ),
                                    (
                                        ApproxExprWithHole::Add {
                                            idx1_pre: Box::new(ApproxExprWithHole::Hole(1)),
                                            idx2_pre: Box::new(ApproxExprWithHole::NoHole(
                                                *approx_expr_idx1,
                                            )),
                                        },
                                        [consts::ZERO, consts::ZERO],
                                    ),
                                ],
                                [*approx_expr_idx1, approx_expr_idx2],
                                &max_num(bound1.clone(), bound2),
                            ),
                            (e, ApproxExpr::Const(c)) => self.on_top(
                                [
                                    (
                                        ApproxExprWithHole::Hole(0),
                                        [consts::ZERO, c.clone() * consts::MAX_SAFE_INTEGER],
                                    ),
                                    (
                                        ApproxExprWithHole::Add {
                                            idx1_pre: Box::new(ApproxExprWithHole::Hole(0)),
                                            idx2_pre: Box::new(ApproxExprWithHole::NoHole(
                                                approx_expr_idx2,
                                            )),
                                        },
                                        [consts::ZERO, consts::ZERO],
                                    ),
                                ],
                                [*approx_expr_idx1, approx_expr_idx2],
                                &max_num(bound1.clone(), bound2),
                            ),
                            (e1, e2) => self.on_top(
                                [
                                    todo!(),
                                    (
                                        ApproxExprWithHole::Add {
                                            idx1_pre: Box::new(ApproxExprWithHole::Hole(0)),
                                            idx2_pre: Box::new(ApproxExprWithHole::Hole(1)),
                                        },
                                        [consts::ZERO, consts::ZERO],
                                    ),
                                ],
                                [*approx_expr_idx1, approx_expr_idx2],
                                &max_num(bound1.clone(), bound2),
                            ),
                        }
                    })
                    .collect(),
                &Expr::Mul { idx1, idx2 } => self
                    .get_approximation(idx1)
                    .iter()
                    .cartesian_product(self.get_approximation(idx2))
                    .flat_map(|((approx_expr_idx1, bound1), (approx_expr_idx2, bound2))| {
                        match (
                            &self.store[*approx_expr_idx1 as usize],
                            &self.store[approx_expr_idx2 as usize],
                        ) {
                            (ApproxExpr::Const(c1), ApproxExpr::Const(c2)) => vec![(
                                self.store_num(c1.clone() * c2.clone()),
                                max_num(bound1.clone(), bound2.clone()),
                            )],
                            (ApproxExpr::Const(c), e) => self.on_top(
                                [
                                    (
                                        ApproxExprWithHole::Hole(1),
                                        [
                                            consts::ZERO,
                                            consts::e_max_safe_integer().pow(c.clone().log10()),
                                        ],
                                    ),
                                    (
                                        ApproxExprWithHole::Mul {
                                            idx1_pre: Box::new(ApproxExprWithHole::Hole(1)),
                                            idx2_pre: Box::new(ApproxExprWithHole::NoHole(
                                                *approx_expr_idx1,
                                            )),
                                        },
                                        [consts::ZERO, consts::ZERO],
                                    ),
                                ],
                                [*approx_expr_idx1, approx_expr_idx2],
                                &max_num(bound1.clone(), bound2),
                            ),
                            (e, ApproxExpr::Const(c)) => self.on_top(
                                [
                                    (
                                        ApproxExprWithHole::Hole(0),
                                        [
                                            consts::ZERO,
                                            consts::e_max_safe_integer().pow(c.clone().log10()),
                                        ],
                                    ),
                                    (
                                        ApproxExprWithHole::Mul {
                                            idx1_pre: Box::new(ApproxExprWithHole::Hole(0)),
                                            idx2_pre: Box::new(ApproxExprWithHole::NoHole(
                                                approx_expr_idx2,
                                            )),
                                        },
                                        [consts::ZERO, consts::ZERO],
                                    ),
                                ],
                                [*approx_expr_idx1, approx_expr_idx2],
                                &max_num(bound1.clone(), bound2),
                            ),
                            (e1, e2) => self.on_top(
                                [
                                    todo!(),
                                    (
                                        ApproxExprWithHole::Mul {
                                            idx1_pre: Box::new(ApproxExprWithHole::Hole(0)),
                                            idx2_pre: Box::new(ApproxExprWithHole::Hole(1)),
                                        },
                                        [consts::ZERO, consts::ZERO],
                                    ),
                                ],
                                [*approx_expr_idx1, approx_expr_idx2],
                                &max_num(bound1.clone(), bound2),
                            ),
                        }
                    })
                    .collect(),
                &Expr::Rec {
                    repeat,
                    rexpr,
                    init,
                } => todo!(),
            };
            self.dst[index as usize] = Some(r);
        }
    }
    fn inverse_upper_bound(&self, approx_expr: &ApproxExpr, bound: &OmegaNum) -> OmegaNum {
        match approx_expr {
            &ApproxExpr::Var(_) => bound.clone(),
            ApproxExpr::Const(c) => {
                if *c >= *bound {
                    consts::ZERO
                } else {
                    consts::INFINITY
                }
            }
            &ApproxExpr::Arrow {
                arrows,
                times,
                payload,
            } => {
                //temporary solution
                min_num(
                    self.inverse_upper_bound_index(times, bound),
                    self.inverse_upper_bound_index(payload, bound),
                )
            }
            &ApproxExpr::Lin {
                expr: LinExpr { mul, add, div },
                idx,
            } => self.inverse_upper_bound_index(
                idx,
                &((bound.clone() * OmegaNum::from(div as f64) - OmegaNum::from(add as f64))
                    / OmegaNum::from(mul as f64)),
            ),
            &ApproxExpr::Exp { base, idx } => self.inverse_upper_bound_index(
                idx,
                &bound.clone().logbase(OmegaNum::from(base as f64)),
            ),
            &ApproxExpr::Add { idx1, idx2 } => min_num(
                self.inverse_upper_bound_index(idx1, bound),
                self.inverse_upper_bound_index(idx2, bound),
            ),
            &ApproxExpr::Mul { idx1, idx2 } => {
                //Are you sure?
                min_num(
                    self.inverse_upper_bound_index(idx1, bound),
                    self.inverse_upper_bound_index(idx2, bound),
                )
            }
            &ApproxExpr::Rec {
                repeat,
                rexpr,
                init,
            } => todo!(),
        }
    }
    fn inverse_upper_bound_index(&self, idx: ApproxExprIdx, bound: &OmegaNum) -> OmegaNum {
        self.inverse_upper_bound(&self.store[idx as usize], bound)
    }
    /// Returns a clone
    pub fn get_approximation(&mut self, index: ExprIdx) -> Vec<BoundedApproxExpr> {
        self.calculate_bounded_approximations(index);
        self.dst[index as usize].clone().unwrap()
    }
}
