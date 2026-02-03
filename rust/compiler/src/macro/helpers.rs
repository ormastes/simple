//! Helper functions for macro evaluation and const value handling
//!
//! This module provides utilities for:
//! - Building constant bindings for macro parameters
//! - Converting evaluated values to their string representations

use simple_parser::ast::{ClassDef, FunctionDef, MacroArg, MacroDef};
use std::collections::HashMap;

use crate::error::CompileError;
use crate::interpreter::{evaluate_expr, Enums, ImplMethods};
use crate::value::{Env, Value};

/// Build constant bindings for macro parameters.
///
/// This function processes macro parameters marked with the `const` keyword
/// and evaluates their corresponding arguments, converting them to string bindings
/// that can be used for compile-time constant substitution.
///
/// # Arguments
/// * `macro_def` - The macro definition containing parameter information
/// * `args` - The arguments passed to the macro invocation
/// * `env` - The current execution environment
/// * `functions` - Available function definitions
/// * `classes` - Available class definitions
/// * `enums` - Available enum definitions
/// * `impl_methods` - Implementation methods for types
///
/// # Returns
/// A HashMap mapping parameter names to their constant string values,
/// or a CompileError if evaluation fails.
pub(crate) fn build_macro_const_bindings(
    macro_def: &MacroDef,
    args: &[MacroArg],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<HashMap<String, String>, CompileError> {
    let mut bindings = HashMap::new();
    for (idx, param) in macro_def.params.iter().enumerate() {
        if !param.is_const {
            continue;
        }
        let Some(MacroArg::Expr(expr)) = args.get(idx) else {
            continue;
        };
        let value = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
        if let Some(text) = const_value_to_string(&value) {
            bindings.insert(param.name.clone(), text);
        }
    }
    Ok(bindings)
}

/// Convert a runtime value to its string representation for const binding.
///
/// This function handles conversion of basic value types to strings that can be
/// used for compile-time constant substitution. Only primitive types are converted;
/// complex types return None.
///
/// Supported types:
/// - String → string value
/// - Symbol → symbol name
/// - Integer → decimal string
/// - Float → decimal string
/// - Boolean → "true" or "false"
/// - Nil → "nil"
/// - All other types → None
///
/// # Arguments
/// * `value` - The value to convert
///
/// # Returns
/// Some(string) for supported types, None for unsupported types.
pub(crate) fn const_value_to_string(value: &Value) -> Option<String> {
    match value {
        Value::Str(s) => Some(s.clone()),
        Value::Symbol(s) => Some(s.clone()),
        Value::Int(i) => Some(i.to_string()),
        Value::Float(f) => Some(f.to_string()),
        Value::Bool(b) => Some(b.to_string()),
        Value::Nil => Some("nil".to_string()),
        _ => None,
    }
}
