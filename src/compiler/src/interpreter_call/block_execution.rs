// Block closure execution helpers for interpreter_call module

use crate::error::CompileError;
use crate::interpreter::{evaluate_expr, pattern_matches};
use crate::value::*;
use simple_parser::ast::{Node, FunctionDef, ClassDef, EnumDef};
use std::collections::HashMap;
use super::bdd::{BDD_INDENT, BDD_CONTEXT_DEFS, BDD_BEFORE_EACH, BDD_AFTER_EACH};

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

fn get_iterator_values(iterable: &Value) -> Result<Vec<Value>, CompileError> {
    match iterable {
        Value::Array(arr) => Ok(arr.clone()),
        Value::Tuple(t) => Ok(t.clone()),
        Value::Str(s) => {
            Ok(s.chars().map(|c| Value::Str(c.to_string())).collect())
        }
        Value::Generator(gen) => {
            Ok(gen.collect_remaining())
        }
        Value::Object { class, fields } => {
            if class == "Range" {
                let start = fields.get("start").and_then(|v| v.as_int().ok()).unwrap_or(0);
                let end = fields.get("end").and_then(|v| v.as_int().ok()).unwrap_or(0);
                let inclusive = fields.get("inclusive").map(|v| v.truthy()).unwrap_or(false);
                let mut values = Vec::new();
                if inclusive {
                    for i in start..=end {
                        values.push(Value::Int(i));
                    }
                } else {
                    for i in start..end {
                        values.push(Value::Int(i));
                    }
                }
                return Ok(values);
            }
            bail_semantic!("Object is not iterable")
        }
        _ => bail_semantic!("Value is not iterable"),
    }
}

/// Execute a block closure (BDD DSL colon-block)
/// Executes each statement in sequence and returns the last expression's value (or Nil)
pub(super) fn exec_block_closure(
    nodes: &[Node],
    captured_env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use super::bdd::exec_block_value;

    let mut local_env = captured_env.clone();
    let mut last_value = Value::Nil;

    for node in nodes {
        match node {
            Node::Expression(expr) => {
                last_value = evaluate_expr(expr, &local_env, functions, classes, enums, impl_methods)?;
            }
            Node::Let(let_stmt) => {
                if let Some(ref value_expr) = let_stmt.value {
                    let val = evaluate_expr(value_expr, &local_env, functions, classes, enums, impl_methods)?;
                    if let simple_parser::ast::Pattern::Identifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MutIdentifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    }
                }
                last_value = Value::Nil;
            }
            Node::Assignment(assign_stmt) => {
                let val = evaluate_expr(&assign_stmt.value, &local_env, functions, classes, enums, impl_methods)?;
                if let simple_parser::ast::Expr::Identifier(name) = &assign_stmt.target {
                    local_env.insert(name.clone(), val);
                }
                last_value = Value::Nil;
            }
            Node::Context(ctx_stmt) => {
                let context_obj = evaluate_expr(&ctx_stmt.context, &local_env, functions, classes, enums, impl_methods)?;

                match &context_obj {
                    Value::Str(name) | Value::Symbol(name) => {
                        let name_str = if matches!(context_obj, Value::Symbol(_)) {
                            format!("with {}", name)
                        } else {
                            name.clone()
                        };

                        let ctx_def_blocks = if matches!(context_obj, Value::Symbol(_)) {
                            BDD_CONTEXT_DEFS.with(|cell| {
                                cell.borrow().get(name).cloned()
                            })
                        } else {
                            None
                        };

                        let indent = BDD_INDENT.with(|cell| *cell.borrow());
                        let indent_str = "  ".repeat(indent);

                        println!("{}{}", indent_str, name_str);

                        BDD_INDENT.with(|cell| *cell.borrow_mut() += 1);

                        BDD_BEFORE_EACH.with(|cell| cell.borrow_mut().push(vec![]));
                        BDD_AFTER_EACH.with(|cell| cell.borrow_mut().push(vec![]));

                        if let Some(ctx_blocks) = ctx_def_blocks {
                            for ctx_block in ctx_blocks {
                                exec_block_value(ctx_block, &local_env, functions, classes, enums, impl_methods)?;
                            }
                        }

                        last_value = exec_block_closure(&ctx_stmt.body.statements, &local_env, functions, classes, enums, impl_methods)?;

                        BDD_BEFORE_EACH.with(|cell| { cell.borrow_mut().pop(); });
                        BDD_AFTER_EACH.with(|cell| { cell.borrow_mut().pop(); });

                        BDD_INDENT.with(|cell| *cell.borrow_mut() -= 1);
                    }
                    _ => {
                        last_value = exec_block_closure(&ctx_stmt.body.statements, &local_env, functions, classes, enums, impl_methods)?;
                    }
                }
            }
            Node::If(if_stmt) => {
                if let Some(pattern) = &if_stmt.let_pattern {
                    let value = evaluate_expr(&if_stmt.condition, &local_env, functions, classes, enums, impl_methods)?;
                    let mut bindings = std::collections::HashMap::new();
                    if pattern_matches(pattern, &value, &mut bindings, enums)? {
                        for (name, val) in bindings {
                            local_env.insert(name, val);
                        }
                        last_value = exec_block_closure_mut(&if_stmt.then_block.statements, &mut local_env, functions, classes, enums, impl_methods)?;
                    } else if let Some(ref else_block) = if_stmt.else_block {
                        last_value = exec_block_closure_mut(&else_block.statements, &mut local_env, functions, classes, enums, impl_methods)?;
                    } else {
                        last_value = Value::Nil;
                    }
                } else {
                    if evaluate_expr(&if_stmt.condition, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                        last_value = exec_block_closure_mut(&if_stmt.then_block.statements, &mut local_env, functions, classes, enums, impl_methods)?;
                    } else if let Some(ref else_block) = if_stmt.else_block {
                        last_value = exec_block_closure_mut(&else_block.statements, &mut local_env, functions, classes, enums, impl_methods)?;
                    } else {
                        last_value = Value::Nil;
                    }
                }
            }
            Node::For(for_stmt) => {
                let iterable = evaluate_expr(&for_stmt.iterable, &local_env, functions, classes, enums, impl_methods)?;
                let iter_values = get_iterator_values(&iterable)?;
                for val in iter_values {
                    if let simple_parser::ast::Pattern::Identifier(ref name) = for_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MutIdentifier(ref name) = for_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    }
                    last_value = exec_block_closure(&for_stmt.body.statements, &local_env, functions, classes, enums, impl_methods)?;
                }
            }
            _ => {
                last_value = Value::Nil;
            }
        }
    }

    Ok(last_value)
}

/// Execute statements in an already-existing mutable environment.
/// Used for if-let blocks where assignments should propagate to the outer scope.
fn exec_block_closure_mut(
    nodes: &[Node],
    local_env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let mut last_value = Value::Nil;

    for node in nodes {
        match node {
            Node::Expression(expr) => {
                last_value = evaluate_expr(expr, local_env, functions, classes, enums, impl_methods)?;
            }
            Node::Let(let_stmt) => {
                if let Some(ref value_expr) = let_stmt.value {
                    let val = evaluate_expr(value_expr, local_env, functions, classes, enums, impl_methods)?;
                    if let simple_parser::ast::Pattern::Identifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MutIdentifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    }
                }
                last_value = Value::Nil;
            }
            Node::Assignment(assign_stmt) => {
                let val = evaluate_expr(&assign_stmt.value, local_env, functions, classes, enums, impl_methods)?;
                if let simple_parser::ast::Expr::Identifier(name) = &assign_stmt.target {
                    local_env.insert(name.clone(), val);
                }
                last_value = Value::Nil;
            }
            _ => {
                last_value = Value::Nil;
            }
        }
    }

    Ok(last_value)
}
