//! Builtin macro invocations
//!
//! Implements builtin macros like println, vec, assert, and dispatches to
//! user-defined macros when appropriate.

use crate::value::{Env, Value};
use crate::{CompileError, evaluate_expr};
use crate::interpreter_unit::{is_unit_type, validate_unit_type};
use simple_parser::ast::*;
use std::cell::RefCell;
use std::collections::HashMap;

use super::expansion::expand_user_macro;

// Note: USER_MACROS is defined in interpreter.rs
thread_local! {
    static USER_MACROS: RefCell<HashMap<String, MacroDef>> = RefCell::new(HashMap::new());
}

pub fn evaluate_macro_invocation(
    name: &str,
    macro_args: &[MacroArg],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    match name {
        "println" => {
            let mut output = String::new();
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                output.push_str(&val.to_display_string());
            }
            println!("{}", output);
            Ok(Value::Nil)
        }
        "print" => {
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                print!("{}", val.to_display_string());
            }
            Ok(Value::Nil)
        }
        "vec" => {
            let mut items = Vec::new();
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                items.push(evaluate_expr(e, env, functions, classes, enums, impl_methods)?);
            }
            Ok(Value::Array(items))
        }
        "assert" => {
            if let Some(MacroArg::Expr(e)) = macro_args.first() {
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                if !val.truthy() {
                    return Err(CompileError::Semantic("assertion failed".into()));
                }
            }
            Ok(Value::Nil)
        }
        "assert_eq" => {
            if macro_args.len() >= 2 {
                let (MacroArg::Expr(left), MacroArg::Expr(right)) = (&macro_args[0], &macro_args[1]);
                let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
                let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;
                if left_val != right_val {
                    return Err(CompileError::Semantic(format!(
                        "assertion failed: {:?} != {:?}",
                        left_val, right_val
                    )));
                }
            }
            Ok(Value::Nil)
        }
        "assert_unit" => {
            // assert_unit!(value, "unit_type") - validate value is of expected unit type
            if macro_args.len() >= 2 {
                let (MacroArg::Expr(value_expr), MacroArg::Expr(type_expr)) =
                    (&macro_args[0], &macro_args[1]);
                let value = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
                let type_val = evaluate_expr(type_expr, env, functions, classes, enums, impl_methods)?;

                // Extract type name from string or symbol
                let type_name = match &type_val {
                    Value::Str(s) => s.clone(),
                    Value::Symbol(s) => s.clone(),
                    _ => {
                        return Err(CompileError::Semantic(
                            "assert_unit: second argument must be a string or symbol representing the unit type".into(),
                        ));
                    }
                };

                // Check if the type is a valid unit type
                if !is_unit_type(&type_name) {
                    return Err(CompileError::Semantic(format!(
                        "assert_unit: '{}' is not a registered unit type (family or compound unit)",
                        type_name
                    )));
                }

                // Validate the value against the unit type
                if let Err(e) = validate_unit_type(&value, &type_name) {
                    return Err(CompileError::Semantic(format!(
                        "unit assertion failed: {}",
                        e
                    )));
                }
            } else {
                return Err(CompileError::Semantic(
                    "assert_unit requires two arguments: assert_unit!(value, \"unit_type\")".into(),
                ));
            }
            Ok(Value::Nil)
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
            Err(CompileError::Semantic(format!("panic: {}", msg)))
        }
        "format" => {
            let mut output = String::new();
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                output.push_str(&val.to_display_string());
            }
            Ok(Value::Str(output))
        }
        "dbg" => {
            if let Some(MacroArg::Expr(e)) = macro_args.first() {
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                eprintln!("[dbg] {:?}", val);
                Ok(val)
            } else {
                Ok(Value::Nil)
            }
        }
        _ => {
            let macro_def = USER_MACROS.with(|cell| cell.borrow().get(name).cloned());
            if let Some(m) = macro_def {
                expand_user_macro(&m, macro_args, env, functions, classes, enums, impl_methods)
            } else {
                Err(CompileError::Semantic(format!("unknown macro: {}!", name)))
            }
        }
    }
}
