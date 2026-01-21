//! InitIR - State initialization instructions
//!
//! Represents the state setup phase executed during component instantiation.

use crate::parser::{Expr, TypeExpr};

/// State initialization IR
#[derive(Debug, Clone, Default)]
pub struct InitIR {
    /// State field definitions
    pub fields: Vec<StateField>,
    /// Server-side initialization instructions
    pub server_init: Vec<InitInstr>,
}

/// A state field declaration
#[derive(Debug, Clone)]
pub struct StateField {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub default: Option<Expr>,
}

/// Initialization instruction
#[derive(Debug, Clone)]
pub enum InitInstr {
    /// Assign value to field
    Assign { field: String, value: Expr },
    /// Execute a database query
    DbQuery {
        result: String,
        query: String,
        params: Vec<Expr>,
    },
    /// Get session value
    SessionGet { result: String, key: String },
    /// Get cookie value
    CookieGet { result: String, name: String },
    /// Execute arbitrary expression
    Eval { result: String, expr: Expr },
}
