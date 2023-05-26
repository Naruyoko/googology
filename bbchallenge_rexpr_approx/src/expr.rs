use indexmap::IndexSet;

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
