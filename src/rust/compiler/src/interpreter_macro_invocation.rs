//! Macro invocation and expansion for the Simple language interpreter
//!
//! This module handles:
//! - Evaluation of built-in macros (println, print, vec, assert, etc.)
//! - User-defined macro expansion with parameter binding
//! - Macro contract processing for introduced symbols
//!
//! The functions in this module are called from the main interpreter_macro.rs
//! to keep the main file focused while extracting reusable macro logic.

use std::collections::HashMap;

use simple_parser::ast::{MacroArg, MacroDef};

use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::{evaluate_expr, ClassDef, Enums, ImplMethods};
use crate::value::{Env, Value};

/// Built-in macro evaluation for println, print, vec, assert, etc.
///
/// # Arguments
///
/// - `name`: The macro name (without the trailing `!`)
/// - `macro_args`: Arguments passed to the macro
/// - `env`: Current lexical environment
/// - `functions`: User-defined functions (mutable for capturing new definitions)
/// - `classes`: User-defined classes
/// - `enums`: Enumeration definitions
/// - `impl_methods`: Implementation method mappings
///
/// # Built-in Macros
///
/// - **println!** - Print arguments to stdout with a newline
/// - **print!** - Print arguments to stdout without a newline
/// - **vec!** - Create a vector from comma-separated expressions
/// - **assert!** - Assert a boolean condition is true
/// - **assert_eq!** - Assert two values are equal
/// - **format!** - Format arguments into a string
/// - **dbg!** - Debug-print a value to stderr and return it
pub fn eval_builtin_macro(
    name: &str,
    macro_args: &[MacroArg],
    env: &mut Env,
    functions: &mut HashMap<String, crate::interpreter::FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Option<Result<Value, CompileError>> {
    match name {
        "println" => {
            let mut output = String::new();
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                output.push_str(&val.to_display_string());
            }
            println!("{}", output);
            Some(Ok(Value::Nil))
        }
        "print" => {
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                print!("{}", val.to_display_string());
            }
            Some(Ok(Value::Nil))
        }
        "vec" => {
            let mut items = Vec::new();
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                items.push(evaluate_expr(e, env, functions, classes, enums, impl_methods)?);
            }
            Some(Ok(Value::Array(items)))
        }
        "assert" => {
            if let Some(MacroArg::Expr(e)) = macro_args.first() {
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                if !val.truthy() {
                    // E3004 - Assertion Failed
                    let ctx = ErrorContext::new()
                        .with_code(codes::ASSERTION_FAILED)
                        .with_help("the assertion condition evaluated to false")
                        .with_note("ensure the condition is true before the assertion");
                    return Some(Err(CompileError::semantic_with_context(
                        "assertion failed".to_string(),
                        ctx,
                    )));
                }
            }
            Some(Ok(Value::Nil))
        }
        "assert_eq" => {
            if macro_args.len() >= 2 {
                let (MacroArg::Expr(left), MacroArg::Expr(right)) = (&macro_args[0], &macro_args[1]);
                let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
                let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;
                if left_val != right_val {
                    // E3004 - Assertion Failed
                    let ctx = ErrorContext::new()
                        .with_code(codes::ASSERTION_FAILED)
                        .with_help("the left and right values are not equal")
                        .with_note(format!("left: {:?}, right: {:?}", left_val, right_val));
                    return Some(Err(CompileError::semantic_with_context(
                        format!("assertion failed: {:?} != {:?}", left_val, right_val),
                        ctx,
                    )));
                }
            }
            Some(Ok(Value::Nil))
        }
        "panic" => {
            let msg = macro_args
                .first()
                .map(|arg| {
                    if let MacroArg::Expr(e) = arg {
                        evaluate_expr(e, env, functions, classes, enums, impl_methods)
                            .map(|v| v.to_display_string())
                            .unwrap_or_else(|_| "panic".into())
                    } else {
                        "panic".into()
                    }
                })
                .unwrap_or_else(|| "explicit panic".into());
            Some(Err(crate::error::factory::panic_with_message(&msg)))
        }
        "format" => {
            let mut output = String::new();
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                output.push_str(&val.to_display_string());
            }
            Some(Ok(Value::Str(output)))
        }
        "dbg" => {
            if let Some(MacroArg::Expr(e)) = macro_args.first() {
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                eprintln!("[dbg] {:?}", val);
                Some(Ok(val))
            } else {
                Some(Ok(Value::Nil))
            }
        }
        _ => None,
    }
}
