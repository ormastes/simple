// Core type definitions and utilities for the interpreter

use std::collections::HashMap;
use simple_parser::ast::{EnumDef, FunctionDef, Type, UnitDef};

/// Check if an expression is a simple identifier (for move tracking)
pub(crate) fn get_identifier_name(expr: &simple_parser::ast::Expr) -> Option<&str> {
    match expr {
        simple_parser::ast::Expr::Identifier(name) => Some(name.as_str()),
        _ => None,
    }
}

/// Extract the variable name from a pattern (for module-level global tracking)
pub(crate) fn get_pattern_name(pattern: &simple_parser::ast::Pattern) -> Option<String> {
    match pattern {
        simple_parser::ast::Pattern::Identifier(name) => Some(name.clone()),
        simple_parser::ast::Pattern::MutIdentifier(name) => Some(name.clone()),
        simple_parser::ast::Pattern::Typed { pattern, .. } => get_pattern_name(pattern),
        _ => None,
    }
}

/// Check if a variable name indicates immutability by naming pattern
/// Returns true if immutable (lowercase), false if mutable (ends with _)
pub(crate) fn is_immutable_by_pattern(name: &str) -> bool {
    if name.is_empty() {
        return true;
    }
    // Mutable if ends with underscore
    if name.ends_with('_') {
        return false;
    }
    // Otherwise immutable
    true
}

/// Stores enum definitions: name -> EnumDef
pub(crate) type Enums = HashMap<String, EnumDef>;

/// Stores impl block methods: type_name -> list of methods
pub(crate) type ImplMethods = HashMap<String, Vec<FunctionDef>>;

/// Stores extern function declarations: name -> definition
pub(crate) type ExternFunctions = HashMap<String, simple_parser::ast::ExternDef>;

/// Stores macro definitions: name -> definition
pub(crate) type Macros = HashMap<String, simple_parser::ast::MacroDef>;

/// Stores unit type definitions: suffix -> UnitDef
pub(crate) type Units = HashMap<String, UnitDef>;

/// Stores unit family definitions: family_name -> (base_type, variants with factors)
/// Used for to_X() conversion methods between related units
pub(crate) type UnitFamilies = HashMap<String, UnitFamilyInfo>;

/// Information about a unit family for conversion support
#[derive(Debug, Clone)]
#[allow(dead_code)] // Fields used when to_X() method dispatch is implemented
pub(crate) struct UnitFamilyInfo {
    /// Base type (e.g., f64)
    pub base_type: Type,
    /// Map of suffix -> conversion factor to base unit
    pub conversions: HashMap<String, f64>,
}

/// Stores trait definitions: trait_name -> TraitDef
pub(crate) type Traits = HashMap<String, simple_parser::ast::TraitDef>;

/// Stores trait implementations: (trait_name, type_name) -> list of methods
/// Used to track which types implement which traits
pub(crate) type TraitImpls = HashMap<(String, String), Vec<FunctionDef>>;

/// Control flow for statement execution.
pub(crate) enum Control {
    Next,
    Return(crate::value::Value),
    #[allow(dead_code)]
    Break(Option<crate::value::Value>),
    Continue,
}
