use super::*;
use simple_parser::ast::Mutability;

/// HIR statement
#[derive(Debug, Clone, PartialEq)]
pub enum HirStmt {
    Let {
        local_index: usize,
        ty: TypeId,
        value: Option<HirExpr>,
    },
    Assign {
        target: HirExpr,
        value: HirExpr,
    },
    Return(Option<HirExpr>),
    Expr(HirExpr),
    If {
        condition: HirExpr,
        then_block: Vec<HirStmt>,
        else_block: Option<Vec<HirStmt>>,
    },
    While {
        condition: HirExpr,
        body: Vec<HirStmt>,
    },
    Loop {
        body: Vec<HirStmt>,
    },
    Break,
    Continue,
}

/// Local variable info
#[derive(Debug, Clone)]
pub struct LocalVar {
    pub name: String,
    pub ty: TypeId,
    pub mutability: Mutability,
    /// Per-parameter DI injection flag (#1013)
    pub inject: bool,
    /// Ghost variable - only exists for verification, erased at runtime
    /// Ghost variables can only be used in verified contexts
    pub is_ghost: bool,
}

impl LocalVar {
    /// Check if this variable is mutable (helper for backwards compatibility)
    pub fn is_mutable(&self) -> bool {
        self.mutability.is_mutable()
    }

    /// Check if this is a ghost variable (verification-only)
    pub fn is_ghost(&self) -> bool {
        self.is_ghost
    }
}
