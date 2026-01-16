use std::collections::HashMap;

use simple_parser::ast::{Expr, LambdaParam, Node};

use super::evaluate_expr;
use crate::error::CompileError;
use crate::value::{Value, ATTR_STRONG};

use super::super::{exec_node, pattern_matches, ClassDef, Control, Enums, Env, FunctionDef, ImplMethods};

pub(super) fn eval_control_expr(
    expr: &Expr,
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    match expr {
        Expr::Lambda {
            capture_all,
            params,
            body,
            move_mode,
        } => {
            let names: Vec<String> = params.iter().map(|LambdaParam { name, .. }| name.clone()).collect();
            // For move closures, we capture by value (clone the environment)
            // For regular closures, we share the environment reference
            // In the interpreter, both behave the same since we clone env anyway
            let captured_env = if move_mode.is_move() { env.clone() } else { env.clone() };
            Ok(Some(Value::Lambda {
                params: names,
                body: body.clone(),
                env: captured_env,
            }))
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            let result = if evaluate_expr(condition, env, functions, classes, enums, impl_methods)?.truthy() {
                evaluate_expr(then_branch, env, functions, classes, enums, impl_methods)?
            } else if let Some(else_b) = else_branch {
                evaluate_expr(else_b, env, functions, classes, enums, impl_methods)?
            } else {
                Value::Nil
            };
            Ok(Some(result))
        }
        Expr::Match { subject, arms } => {
            let subject_val = evaluate_expr(subject, env, functions, classes, enums, impl_methods)?;

            // Check pattern exhaustiveness for enums
            if let Value::Enum { enum_name, .. } = &subject_val {
                if let Some(enum_def) = enums.get(enum_name) {
                    let is_strong = enum_def.attributes.iter().any(|attr| attr.name == ATTR_STRONG);

                    // For strong enums, disallow wildcard/catch-all patterns
                    if is_strong {
                        for arm in arms {
                            if super::super::is_catch_all_pattern(&arm.pattern) {
                                return Err(CompileError::Semantic(format!(
                                    "strong enum '{}' does not allow wildcard or catch-all patterns in match",
                                    enum_name
                                )));
                            }
                        }
                    }

                    // Check exhaustiveness for all enums
                    let variants: Vec<String> = enum_def.variants.iter().map(|v| v.name.clone()).collect();
                    let (is_exhaustive, missing) =
                        crate::pattern_analysis::check_enum_exhaustiveness(enum_name, &variants, arms);

                    if !is_exhaustive {
                        tracing::warn!(
                            "Non-exhaustive pattern match for enum '{}': missing variants: {}",
                            enum_name,
                            missing.join(", ")
                        );
                    }
                }
            }

            for arm in arms {
                let mut arm_bindings = HashMap::new();
                if pattern_matches(&arm.pattern, &subject_val, &mut arm_bindings, enums)? {
                    if let Some(guard) = &arm.guard {
                        let mut guard_env = env.clone();
                        for (name, value) in &arm_bindings {
                            guard_env.insert(name.clone(), value.clone());
                        }
                        let guard_result =
                            evaluate_expr(guard, &mut guard_env, functions, classes, enums, impl_methods)?;
                        if !guard_result.truthy() {
                            continue;
                        }
                    }
                    let mut arm_env = env.clone();
                    for (name, value) in arm_bindings {
                        arm_env.insert(name, value);
                    }
                    let mut result = Value::Nil;
                    for stmt in &arm.body.statements {
                        match exec_node(stmt, &mut arm_env, functions, classes, enums, impl_methods)? {
                            Control::Return(v) => return Ok(Some(v)),
                            Control::Break(_) => return Ok(Some(Value::Nil)),
                            Control::Continue => break,
                            Control::Next => {
                                if let Node::Expression(expr) = stmt {
                                    result =
                                        evaluate_expr(expr, &mut arm_env, functions, classes, enums, impl_methods)?;
                                }
                            }
                        }
                    }
                    return Ok(Some(result));
                }
            }
            Err(CompileError::Semantic("match exhausted: no pattern matched".into()))
        }
        Expr::DoBlock(nodes) => Ok(Some(Value::BlockClosure {
            nodes: nodes.clone(),
            env: env.clone(),
        })),
        _ => Ok(None),
    }
}
