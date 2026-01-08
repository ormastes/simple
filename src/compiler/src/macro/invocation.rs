use super::expansion::expand_user_macro;
use crate::error::CompileError;
use crate::interpreter::{evaluate_expr, ClassDef, Enums, FunctionDef, ImplMethods};
use crate::value::{Env, Value};
use simple_parser::ast::{BinOp, Expr, MacroArg};
use std::collections::HashMap;

/// Convert an expression to its source code string representation
fn expr_to_source_string(expr: &Expr) -> String {
    match expr {
        Expr::Integer(i) => i.to_string(),
        Expr::Float(f) => f.to_string(),
        Expr::Bool(b) => b.to_string(),
        Expr::String(s) => format!("\"{}\"", s),
        Expr::Identifier(name) => name.clone(),
        Expr::Binary { op, left, right } => {
            let op_str = match op {
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "*",
                BinOp::Div => "/",
                BinOp::Mod => "%",
                BinOp::Eq => "==",
                BinOp::NotEq => "!=",
                BinOp::Lt => "<",
                BinOp::LtEq => "<=",
                BinOp::Gt => ">",
                BinOp::GtEq => ">=",
                BinOp::And => "and",
                BinOp::Or => "or",
                _ => "?",
            };
            format!(
                "({} {} {})",
                expr_to_source_string(left),
                op_str,
                expr_to_source_string(right)
            )
        }
        Expr::Unary { op, operand } => {
            let op_str = match op {
                simple_parser::ast::UnaryOp::Neg => "-",
                simple_parser::ast::UnaryOp::Not => "not ",
                _ => "?",
            };
            format!("{}{}", op_str, expr_to_source_string(operand))
        }
        Expr::Call { callee, args } => {
            let args_str: Vec<String> = args.iter().map(|a| expr_to_source_string(&a.value)).collect();
            format!("{}({})", expr_to_source_string(callee), args_str.join(", "))
        }
        Expr::MethodCall { receiver, method, args } => {
            let args_str: Vec<String> = args.iter().map(|a| expr_to_source_string(&a.value)).collect();
            format!(
                "{}.{}({})",
                expr_to_source_string(receiver),
                method,
                args_str.join(", ")
            )
        }
        Expr::FieldAccess { receiver, field } => {
            format!("{}.{}", expr_to_source_string(receiver), field)
        }
        Expr::Index { receiver, index } => {
            format!(
                "{}[{}]",
                expr_to_source_string(receiver),
                expr_to_source_string(index)
            )
        }
        Expr::Array(items) => {
            let items_str: Vec<String> = items.iter().map(|i| expr_to_source_string(i)).collect();
            format!("[{}]", items_str.join(", "))
        }
        Expr::Tuple(items) => {
            let items_str: Vec<String> = items.iter().map(|i| expr_to_source_string(i)).collect();
            format!("({})", items_str.join(", "))
        }
        Expr::Lambda { params, .. } => {
            let params_str: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
            format!("fn({}) -> ...", params_str.join(", "))
        }
        Expr::If { condition, else_branch, .. } => {
            let else_str = else_branch
                .as_ref()
                .map(|e| format!(" else {}", expr_to_source_string(e)))
                .unwrap_or_default();
            format!("if {}: ...{}", expr_to_source_string(condition), else_str)
        }
        Expr::Nil => "nil".to_string(),
        _ => format!("{:?}", expr), // Fallback for complex expressions
    }
}

pub(crate) fn evaluate_macro_invocation(
    name: &str,
    macro_args: &[MacroArg],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
                let (MacroArg::Expr(left), MacroArg::Expr(right)) =
                    (&macro_args[0], &macro_args[1]);
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
                if !crate::interpreter::is_unit_type(&type_name) {
                    return Err(CompileError::Semantic(format!(
                        "assert_unit: '{}' is not a registered unit type (family or compound unit)",
                        type_name
                    )));
                }

                // Validate the value against the unit type
                if let Err(e) = crate::interpreter::validate_unit_type(&value, &type_name) {
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
        "stringify" => {
            // Convert expression to its source code string representation
            if let Some(MacroArg::Expr(e)) = macro_args.first() {
                Ok(Value::Str(expr_to_source_string(e)))
            } else {
                Ok(Value::Str(String::new()))
            }
        }
        _ => {
            let macro_def = crate::interpreter::USER_MACROS.with(|cell| cell.borrow().get(name).cloned());
            if let Some(m) = macro_def {
                expand_user_macro(&m, macro_args, env, functions, classes, enums, impl_methods)
            } else {
                Err(CompileError::Semantic(format!("unknown macro: {}!", name)))
            }
        }
    }
}
