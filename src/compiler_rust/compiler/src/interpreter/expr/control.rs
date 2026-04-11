use std::sync::Arc;
use std::collections::{HashMap, HashSet};

use simple_parser::ast::{Expr, LambdaParam, Node};
use simple_parser::FStringPart;

use super::evaluate_expr;
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Value, ATTR_STRONG};

use super::super::{
    exec_node, exec_block_fn, exec_if_expr, exec_match_expr, pattern_matches, ClassDef, Control, Enums, Env,
    FunctionDef, ImplMethods,
};
use crate::value::CowEnv;

pub(super) fn eval_control_expr(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
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
            let captured_env = if *capture_all {
                Arc::new(env.clone())
            } else {
                // Selective capture: only copy variables referenced in the lambda body
                let used = collect_free_vars(body);
                let filtered: HashMap<String, Value> = env
                    .iter()
                    .filter(|(k, _)| used.contains(k.as_str()))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();
                Arc::new(CowEnv::from_map(filtered))
            };
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
            let branch_result = if evaluate_expr(condition, env, functions, classes, enums, impl_methods)?.truthy() {
                evaluate_expr(then_branch, env, functions, classes, enums, impl_methods)?
            } else if let Some(else_b) = else_branch {
                evaluate_expr(else_b, env, functions, classes, enums, impl_methods)?
            } else {
                Value::Nil
            };
            // If branch returned a BlockClosure (from DoBlock), execute it immediately
            // This handles the case where if branches are parsed as DoBlock expressions
            let result = if let Value::BlockClosure {
                nodes,
                env: captured_env,
            } = branch_result
            {
                let mut block_env = Env::clone(&captured_env);
                let mut block = simple_parser::ast::Block::default();
                block.statements = nodes;
                let (flow, last_val) = exec_block_fn(&block, &mut block_env, functions, classes, enums, impl_methods)?;
                // Write back mutations from block_env to the outer env.
                // This ensures that me-method self-updates inside if-expression
                // branches propagate correctly.
                for (key, value) in &block_env {
                    if env.contains_key(key) {
                        env.insert(key.clone(), value.clone());
                    }
                }
                match flow {
                    Control::Return(v) => return Ok(Some(v)),
                    _ => last_val.unwrap_or(Value::Nil),
                }
            } else {
                branch_result
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
                                let ctx = ErrorContext::new().with_code(codes::INVALID_PATTERN).with_help(format!(
                                    "strong enum '{}' requires all variants to be explicitly matched",
                                    enum_name
                                ));
                                return Err(CompileError::semantic_with_context(
                                    format!("invalid pattern: strong enum '{}' does not allow wildcard or catch-all patterns in match", enum_name),
                                    ctx,
                                ));
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

            // Check boolean exhaustiveness
            if matches!(&subject_val, Value::Bool(_)) {
                let analysis = crate::pattern_analysis::analyze_match(arms);
                if !analysis.is_exhaustive && !analysis.missing_patterns.is_empty() {
                    let missing_str = analysis.missing_patterns.join(", ");
                    tracing::warn!("Non-exhaustive pattern match on boolean: missing {}", missing_str);
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
                    let stmt_count = arm.body.statements.len();
                    for (idx, stmt) in arm.body.statements.iter().enumerate() {
                        let is_last = idx == stmt_count - 1;

                        // For the last statement, handle if/match specially to capture implicit return
                        if is_last {
                            match stmt {
                                Node::Expression(expr) => {
                                    result =
                                        evaluate_expr(expr, &mut arm_env, functions, classes, enums, impl_methods)?;
                                    continue;
                                }
                                Node::If(if_stmt) => {
                                    // Use exec_if_expr to properly capture the implicit return value
                                    result =
                                        exec_if_expr(if_stmt, &mut arm_env, functions, classes, enums, impl_methods)?;
                                    continue;
                                }
                                Node::Match(match_stmt) => {
                                    // Use exec_match_expr to properly capture the implicit return value
                                    result = exec_match_expr(
                                        match_stmt,
                                        &mut arm_env,
                                        functions,
                                        classes,
                                        enums,
                                        impl_methods,
                                    )?;
                                    continue;
                                }
                                _ => {}
                            }
                        }

                        match exec_node(stmt, &mut arm_env, functions, classes, enums, impl_methods)? {
                            Control::Return(v) => return Ok(Some(v)),
                            Control::Break(..) => return Ok(Some(Value::Nil)),
                            Control::Continue(_) => break,
                            Control::Next => {
                                if let Node::Expression(expr) = stmt {
                                    result =
                                        evaluate_expr(expr, &mut arm_env, functions, classes, enums, impl_methods)?;
                                }
                            }
                        }
                    }
                    // Write back pre-existing variables from arm_env to env
                    for (key, value) in &arm_env {
                        if env.contains_key(key) {
                            env.insert(key.clone(), value.clone());
                        }
                    }
                    return Ok(Some(result));
                }
            }
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_PATTERN)
                .with_help("add a wildcard pattern (_) or another pattern to handle this case");
            Err(CompileError::semantic_with_context(
                "invalid pattern: match expression exhausted without matching any pattern",
                ctx,
            ))
        }
        Expr::DoBlock(nodes) => Ok(Some(Value::BlockClosure {
            nodes: nodes.clone(),
            env: Arc::new(env.clone()),
        })),
        _ => Ok(None),
    }
}

/// Collect all free variable references in an expression tree.
///
/// Walks the AST and gathers every `Identifier` name that appears.
/// Used for selective lambda capture: only the variables actually
/// referenced in the lambda body are copied into the captured env.
fn collect_free_vars(expr: &Expr) -> HashSet<String> {
    let mut vars = HashSet::new();
    collect_free_vars_recursive(expr, &mut vars);
    vars
}

/// Recursively walk the expression tree and collect identifier names.
fn collect_free_vars_recursive(expr: &Expr, vars: &mut HashSet<String>) {
    match expr {
        Expr::Identifier(name) => {
            vars.insert(name.clone());
        }
        Expr::Binary { left, right, .. } => {
            collect_free_vars_recursive(left, vars);
            collect_free_vars_recursive(right, vars);
        }
        Expr::Unary { operand, .. } => {
            collect_free_vars_recursive(operand, vars);
        }
        Expr::Call { callee, args } => {
            collect_free_vars_recursive(callee, vars);
            for arg in args {
                collect_free_vars_recursive(&arg.value, vars);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_free_vars_recursive(receiver, vars);
            for arg in args {
                collect_free_vars_recursive(&arg.value, vars);
            }
        }
        Expr::FieldAccess { receiver, .. } => {
            collect_free_vars_recursive(receiver, vars);
        }
        Expr::Index { receiver, index } => {
            collect_free_vars_recursive(receiver, vars);
            collect_free_vars_recursive(index, vars);
        }
        Expr::Tuple(exprs) | Expr::Array(exprs) | Expr::VecLiteral(exprs) => {
            for e in exprs {
                collect_free_vars_recursive(e, vars);
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            collect_free_vars_recursive(condition, vars);
            collect_free_vars_recursive(then_branch, vars);
            if let Some(eb) = else_branch {
                collect_free_vars_recursive(eb, vars);
            }
        }
        Expr::Lambda { body, .. } => {
            // Walk into nested lambdas — their free vars are also our free vars
            collect_free_vars_recursive(body, vars);
        }
        Expr::Cast { expr, .. } => {
            collect_free_vars_recursive(expr, vars);
        }
        Expr::FString { parts, .. } => {
            for part in parts {
                match part {
                    FStringPart::Expr(e) | FStringPart::ExprWithFormat(e, _) => {
                        collect_free_vars_recursive(e, vars);
                    }
                    _ => {}
                }
            }
        }
        Expr::StructInit { fields, .. } => {
            for (_, value) in fields {
                collect_free_vars_recursive(value, vars);
            }
        }
        Expr::New { expr, .. } => {
            collect_free_vars_recursive(expr, vars);
        }
        Expr::Yield(Some(v)) => {
            collect_free_vars_recursive(v, vars);
        }
        Expr::Yield(None) => {}
        Expr::Spawn(inner) => {
            collect_free_vars_recursive(inner, vars);
        }
        Expr::Match { subject, arms } => {
            collect_free_vars_recursive(subject, vars);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_free_vars_recursive(guard, vars);
                }
                for stmt in &arm.body.statements {
                    if let Node::Expression(e) = stmt {
                        collect_free_vars_recursive(e, vars);
                    }
                }
            }
        }
        Expr::DoBlock(nodes) => {
            for stmt in nodes {
                if let Node::Expression(e) = stmt {
                    collect_free_vars_recursive(e, vars);
                }
            }
        }
        // Literals and other expressions that don't contain variable references
        _ => {}
    }
}
