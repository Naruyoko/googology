use indexmap::IndexSet;

mod omega_num;
use omega_num::OmegaNum;

use crate::omega_num::consts;

pub type VarId = u8;
pub type DivT = u64;
pub type ExprIdx = u16;
pub type Exprs = IndexSet<Expr>;

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

pub struct LinExpr {
    pub mul: u16,
    pub add: i16,
    pub div: DivT,
}

fn main() {
    println!("Hello, world!");
    println!(
        "{}",
        OmegaNum::new(100.1, vec![2, 1, 0, 13, 3, 1], false).to_string()
    );
    for i in 1..10 {
        println!(
            "{}",
            OmegaNum::arrow(OmegaNum::from(i as f64), OmegaNum::from(i as f64), 2).to_string()
        )
    }
    for i in 1..10 {
        println!(
            "{}",
            OmegaNum::arrow(OmegaNum::from(i as f64), OmegaNum::from(i as f64), 3).to_string()
        )
    }
    for i in 1..10 {
        println!(
            "{}",
            OmegaNum::arrow(OmegaNum::from(3.0), OmegaNum::from(3.0), i).to_string()
        )
    }
}
