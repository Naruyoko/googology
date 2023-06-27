use indexmap::IndexSet;

pub type VarId = u8;
pub type DivT = u64;
pub type ExprIdx = u16;
pub type Exprs = IndexSet<Expr>;

#[derive(Debug, Clone)]
pub enum Expr {
    Var(VarId),
    Const(u16),
    Lin {
        expr: LinExpr,
        idx: ExprIdx,
    },
    Exp {
        base: u16,
        idx: ExprIdx,
    },
    Add {
        idx1: ExprIdx,
        idx2: ExprIdx,
    },
    Mul {
        idx1: ExprIdx,
        idx2: ExprIdx,
    },
    Rec {
        repeat: ExprIdx,
        rexpr: ExprIdx,
        init: ExprIdx,
    },
}
#[derive(Debug, Clone)]
pub struct LinExpr {
    pub mul: u16,
    pub add: i16,
    pub div: DivT,
}
pub fn shallow_to_string(expr: &Expr) -> String {
    match expr {
        &Expr::Var(_) => format!("b"),
        &Expr::Const(c) => format!("{c}"),
        &Expr::Lin {
            expr: LinExpr { mul, add, div },
            idx,
        } => {
            format!("({mul}*#{idx}+{add})/{div}")
        }
        &Expr::Exp { base, idx } => format!("{base}^#{idx}"),
        &Expr::Add { idx1, idx2 } => format!("#{idx1}+#{idx2}"),
        &Expr::Mul { idx1, idx2 } => format!("#{idx1}*#{idx2}"),
        &Expr::Rec {
            repeat,
            rexpr,
            init,
        } => format!("<#{repeat},#{rexpr},#{init}>"),
    }
}
pub fn deep_to_string(exprs: &Exprs, idx: ExprIdx) -> String {
    let mut s = format!("#{idx}");
    while s.contains("#") {
        let start_index = s.find("#").unwrap();
        let end_index = start_index + s[start_index..].find("}").unwrap();
        s.replace_range(
            start_index..=end_index,
            &shallow_to_string(
                exprs
                    .get_index(
                        ExprIdx::from_str_radix(&s[start_index + 2..end_index], 10).unwrap()
                            as usize,
                    )
                    .unwrap(),
            ),
        )
    }
    s
}
