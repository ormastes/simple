use std::sync::Arc;
use std::collections::{HashMap, HashSet};

use simple_parser::ast::{DeferBody, Expr, LambdaParam, Node, Pattern};
use simple_parser::FStringPart;

use super::evaluate_expr;
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Value, ATTR_STRONG};

use super::super::{
    exec_node, exec_block_fn, exec_if_expr, exec_if_core, exec_match_expr, exec_match_core, pattern_matches, ClassDef,
    Control, Enums, Env, FunctionDef, ImplMethods,
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
            if std::env::var("SIMPLE_DEBUG_LAMBDA_SYNC").is_ok() {
                eprintln!(
                    "[lambda-capture] cur_mod={:?} bindings_by_owner={:?} capture_all={} env_bindings={:?} free={:?}",
                    crate::interpreter::CURRENT_EXEC_MODULE.with(|c| c.borrow().clone()),
                    crate::interpreter::MODULE_GLOBAL_BINDINGS_BY_OWNER.with(|c| c
                        .borrow()
                        .iter()
                        .map(|(o, m)| (o.to_string(), m.keys().cloned().collect::<Vec<_>>()))
                        .collect::<Vec<_>>()),
                    capture_all,
                    env.global_bindings()
                        .map(|(k, (o, s))| (k.clone(), o.to_string(), s.clone()))
                        .collect::<Vec<_>>(),
                    collect_free_vars(body),
                );
            }
            // For move closures, we capture by value (clone the environment)
            // For regular closures, we share the environment reference
            // In the interpreter, both behave the same since we clone env anyway
            let captured_env = if *capture_all {
                Arc::new(env.clone())
            } else {
                // Selective capture: only copy variables referenced in the lambda
                // body. Must preserve global-binding metadata — a plain
                // name->value map demotes imported global aliases to locals,
                // which loses their defining owner and recreates the stage-4
                // stale-arena-index class of bug on lambda global writes.
                let used = collect_free_vars(body);
                let used: HashSet<String> = used.iter().map(|s| s.to_string()).collect();
                Arc::new(env.project_preserving_bindings(&used))
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
            let cond_val = evaluate_expr(condition, env, functions, classes, enums, impl_methods)?;
            // `is_condition_present` (not plain `.truthy()`): see its doc
            // comment in `interpreter_control.rs` -- `x = if opt.?: a else:
            // b` has the same "0 is falsy" landmine as the statement form
            // (`exec_if`/`exec_if_core`) if `.?`'s presence decision is
            // re-derived from the payload's truthiness instead of trusted.
            let branch_result = if crate::interpreter::interpreter_control::is_condition_present(condition, &cond_val) {
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
                let mut block_env = Env::clone(&*captured_env);
                // Dirty-only write-back: copying every shared key would replay
                // the closure's stale captured snapshot over values a deeper
                // call wrote after capture.
                block_env.clear_dirty();
                let mut block = simple_parser::ast::Block {
                    statements: nodes,
                    ..Default::default()
                };
                let (flow, last_val) = exec_block_fn(&block, &mut block_env, functions, classes, enums, impl_methods)?;
                // Write back mutations from block_env to the outer env.
                // This ensures that me-method self-updates inside if-expression
                // branches propagate correctly. Dirty-only + refresh channel:
                // see copy_back_block_writes.
                crate::interpreter::block_exec::copy_back_block_writes(&block_env, env);
                match flow {
                    // A `return` inside an if/match EXPRESSION arm must propagate out of the
                    // function, not become the expression's value. Reuse the `?`-operator
                    // early-return channel (TryError), which is already caught at every
                    // function/method/lambda/class boundary. See bug
                    // interp_return_in_match_expr_swallowed_2026-06-30.
                    Control::Return(v) => return Err(CompileError::TryError(Box::new(v))),
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
                if pattern_matches(&arm.pattern, &subject_val, &mut arm_bindings, enums, classes)? {
                    if let Some(guard) = &arm.guard {
                        let mut guard_env = env.clone();
                        for (name, value) in &arm_bindings {
                            guard_env.insert(name.clone(), value.clone());
                        }
                        let guard_result =
                            evaluate_expr(guard, &mut guard_env, functions, classes, enums, impl_methods)?;
                        if !crate::interpreter::interpreter_control::is_condition_present(guard, &guard_result) {
                            continue;
                        }
                    }
                    let mut arm_env = env.clone();
                    let binding_names: std::collections::HashSet<String> =
                        arm_bindings.keys().cloned().collect();
                    for (name, value) in arm_bindings {
                        arm_env.insert(name.clone(), value);
                        // Mark the arm binding LOCAL so reads don't prefer
                        // MODULE_GLOBALS (match-expression form of the
                        // `case Ok(engine):` module-dict bug).
                        arm_env.enter_block_local(name);
                    }
                    let mut result = Value::Nil;
                    let stmt_count = arm.body.statements.len();
                    for (idx, stmt) in arm.body.statements.iter().enumerate() {
                        let is_last = idx == stmt_count - 1;

                        // For the last statement, handle if/match specially to capture implicit return.
                        // Use the *_core variants so explicit `return` statements inside the arm
                        // propagate upward rather than being collapsed into a value.
                        if is_last {
                            match stmt {
                                Node::Expression(expr) => {
                                    result =
                                        evaluate_expr(expr, &mut arm_env, functions, classes, enums, impl_methods)?;
                                    continue;
                                }
                                Node::If(if_stmt) => {
                                    let (flow, val) =
                                        exec_if_core(if_stmt, &mut arm_env, functions, classes, enums, impl_methods)?;
                                    match flow {
                                        Control::Next => {
                                            result = val;
                                        }
                                        // A `return` inside an if/match EXPRESSION arm must propagate out of the
                                        // function, not become the expression's value. Reuse the `?`-operator
                                        // early-return channel (TryError), which is already caught at every
                                        // function/method/lambda/class boundary. See bug
                                        // interp_return_in_match_expr_swallowed_2026-06-30.
                                        Control::Return(v) => return Err(CompileError::TryError(Box::new(v))),
                                        Control::Break(..) => return Ok(Some(Value::Nil)),
                                        Control::Continue(_) => break,
                                    }
                                    continue;
                                }
                                Node::Match(match_stmt) => {
                                    let (flow, last_val) = exec_match_core(
                                        match_stmt,
                                        &mut arm_env,
                                        functions,
                                        classes,
                                        enums,
                                        impl_methods,
                                    )?;
                                    match flow {
                                        Control::Next => {
                                            result = last_val.unwrap_or(Value::Nil);
                                        }
                                        // A `return` inside an if/match EXPRESSION arm must propagate out of the
                                        // function, not become the expression's value. Reuse the `?`-operator
                                        // early-return channel (TryError), which is already caught at every
                                        // function/method/lambda/class boundary. See bug
                                        // interp_return_in_match_expr_swallowed_2026-06-30.
                                        Control::Return(v) => return Err(CompileError::TryError(Box::new(v))),
                                        Control::Break(..) => return Ok(Some(Value::Nil)),
                                        Control::Continue(_) => break,
                                    }
                                    continue;
                                }
                                _ => {}
                            }
                        }

                        match exec_node(stmt, &mut arm_env, functions, classes, enums, impl_methods)? {
                            // A `return` inside an if/match EXPRESSION arm must propagate out of the
                            // function, not become the expression's value. Reuse the `?`-operator
                            // early-return channel (TryError), which is already caught at every
                            // function/method/lambda/class boundary. See bug
                            // interp_return_in_match_expr_swallowed_2026-06-30.
                            Control::Return(v) => return Err(CompileError::TryError(Box::new(v))),
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
                    // Write back pre-existing variables from arm_env to env.
                    // Arm PATTERN BINDINGS are arm-local and must never be
                    // written back: `Some(value): value` leaked `value` (a
                    // BeDomNode) past its arm whenever the enclosing frame's
                    // base env happened to contain a same-named key, shadowing
                    // a later `val value` — "method `len` not found on type
                    // `BeDomNode`" in browser_session_runtime (5th match-arm
                    // leak site, 2026-08-19).
                    for (key, value) in &arm_env {
                        if binding_names.contains(key) {
                            continue;
                        }
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
            let arm_patterns = arms
                .iter()
                .map(|arm| format!("{}:{} {:?}", arm.span.line, arm.span.column, arm.pattern))
                .collect::<Vec<_>>()
                .join(", ");
            Err(CompileError::semantic_with_context(
                format!(
                    "invalid pattern: match expression exhausted without matching any pattern for {} value {}; arms [{}]",
                    subject_val.type_name(),
                    subject_val.to_display_string(),
                    arm_patterns
                ),
                ctx,
            ))
        }
        Expr::DoBlock(nodes) => Ok(Some(Value::BlockClosure {
            nodes: nodes.clone(),
            env: Arc::new(env.clone()),
        })),
        Expr::UnsafeBlock(nodes) => {
            let (flow, last_value) =
                super::super::exec_unsafe_block(nodes, env, functions, classes, enums, impl_methods)?;
            match flow {
                Control::Return(value) => Err(CompileError::TryError(Box::new(value))),
                Control::Break(value, _) => Err(CompileError::LoopBreak(value)),
                Control::Continue(_) => Err(CompileError::LoopContinue),
                Control::Next => Ok(Some(last_value.unwrap_or(Value::Nil))),
            }
        }
        _ => Ok(None),
    }
}

/// Collect all free variable references in an expression tree.
///
/// Walks the AST -- expressions **and every statement form inside blocks** --
/// and gathers every `Identifier` name that is *free*: referenced without being
/// bound earlier inside the walked body by a `val`/`var`, a `for` binder, an
/// `if let`/`while let` pattern, a match-arm pattern, a `with ... as` name, or a
/// nested lambda parameter.
///
/// Used for selective lambda capture: only the variables actually referenced in
/// the lambda body are copied into the captured env.
///
/// History: this walker used to descend only into `Node::Expression` statements,
/// so an outer local read from a `val` initializer, an assignment, an
/// `if`/`for`/`while`/`match` body, or a `return` was never captured and then
/// resolved as missing at runtime (a hard error in the interpreter, a silent `0`
/// under the JIT). See
/// `doc/08_tracking/bug/closure_selective_capture_skips_non_expression_statements_2026-07-27.md`.
///
/// Direction of error matters: over-capturing is harmless (the filter is only an
/// optimisation), under-capturing is a correctness bug. Shadowing is still
/// honoured so an inner binder never drags the wrong outer value into the env --
/// and it is honoured *sequentially*, so `val x = x` still captures the outer
/// `x` for its own initializer.
fn collect_free_vars(expr: &Expr) -> HashSet<String> {
    let mut vars = HashSet::new();
    let mut bound: Vec<String> = Vec::new();
    collect_free_vars_recursive(expr, &mut bound, &mut vars);
    vars
}

/// Record `name` as free unless an enclosing binder inside the walked body owns it.
fn note_free_var(name: &str, bound: &[String], vars: &mut HashSet<String>) {
    if !bound.iter().any(|b| b == name) {
        vars.insert(name.to_string());
    }
}

/// Add every name a pattern binds to `bound`; literal/range patterns instead
/// *read* their sub-expressions.
fn bind_pattern_vars(pattern: &Pattern, bound: &mut Vec<String>, vars: &mut HashSet<String>) {
    match pattern {
        Pattern::Identifier(name) | Pattern::MutIdentifier(name) | Pattern::MoveIdentifier(name) => {
            bound.push(name.clone());
        }
        Pattern::Tuple(pats) | Pattern::Array(pats) | Pattern::Or(pats) => {
            for p in pats {
                bind_pattern_vars(p, bound, vars);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, p) in fields {
                bind_pattern_vars(p, bound, vars);
            }
        }
        Pattern::Enum { payload: Some(pats), .. } => {
            for p in pats {
                bind_pattern_vars(p, bound, vars);
            }
        }
        Pattern::Typed { pattern, .. } => bind_pattern_vars(pattern, bound, vars),
        Pattern::Literal(e) => collect_free_vars_recursive(e, bound, vars),
        Pattern::Range { start, end, .. } => {
            collect_free_vars_recursive(start, bound, vars);
            collect_free_vars_recursive(end, bound, vars);
        }
        Pattern::Wildcard | Pattern::Rest | Pattern::Enum { payload: None, .. } => {}
    }
}

/// Walk a statement list as a lexical scope: binders introduced inside it are
/// visible to the statements that follow, and dropped at the end of the block.
fn collect_free_vars_block(stmts: &[Node], bound: &mut Vec<String>, vars: &mut HashSet<String>) {
    let mark = bound.len();
    for stmt in stmts {
        collect_free_vars_stmt(stmt, bound, vars);
    }
    bound.truncate(mark);
}

fn collect_free_vars_arms(arms: &[simple_parser::ast::MatchArm], bound: &mut Vec<String>, vars: &mut HashSet<String>) {
    for arm in arms {
        let mark = bound.len();
        bind_pattern_vars(&arm.pattern, bound, vars);
        if let Some(guard) = &arm.guard {
            collect_free_vars_recursive(guard, bound, vars);
        }
        collect_free_vars_block(&arm.body.statements, bound, vars);
        bound.truncate(mark);
    }
}

fn collect_free_vars_defer(body: &DeferBody, bound: &mut Vec<String>, vars: &mut HashSet<String>) {
    match body {
        DeferBody::Expr(e) => collect_free_vars_recursive(e, bound, vars),
        DeferBody::Block(b) => collect_free_vars_block(&b.statements, bound, vars),
    }
}

/// Walk a single statement, collecting free reads and registering its binders.
fn collect_free_vars_stmt(stmt: &Node, bound: &mut Vec<String>, vars: &mut HashSet<String>) {
    match stmt {
        Node::Expression(e) => collect_free_vars_recursive(e, bound, vars),
        Node::Let(l) => {
            // Initializer is evaluated BEFORE the binder exists: `val x = x`
            // reads the outer `x`.
            if let Some(v) = &l.value {
                collect_free_vars_recursive(v, bound, vars);
            }
            bind_pattern_vars(&l.pattern, bound, vars);
        }
        Node::Const(c) => {
            collect_free_vars_recursive(&c.value, bound, vars);
            bound.push(c.name.clone());
        }
        Node::Static(s) => {
            collect_free_vars_recursive(&s.value, bound, vars);
            bound.push(s.name.clone());
        }
        Node::Assignment(a) => {
            // The target counts as a read: compound ops (`x += 1`) read it, and
            // `x.f = v` / `x[i] = v` need the receiver present either way.
            collect_free_vars_recursive(&a.target, bound, vars);
            collect_free_vars_recursive(&a.value, bound, vars);
        }
        Node::Return(r) => {
            if let Some(v) = &r.value {
                collect_free_vars_recursive(v, bound, vars);
            }
        }
        Node::If(i) => {
            let mark = bound.len();
            collect_free_vars_recursive(&i.condition, bound, vars);
            if let Some(p) = &i.let_pattern {
                bind_pattern_vars(p, bound, vars);
            }
            collect_free_vars_block(&i.then_block.statements, bound, vars);
            bound.truncate(mark);
            for (pat, cond, blk) in &i.elif_branches {
                let elif_mark = bound.len();
                collect_free_vars_recursive(cond, bound, vars);
                if let Some(p) = pat {
                    bind_pattern_vars(p, bound, vars);
                }
                collect_free_vars_block(&blk.statements, bound, vars);
                bound.truncate(elif_mark);
            }
            if let Some(eb) = &i.else_block {
                collect_free_vars_block(&eb.statements, bound, vars);
            }
        }
        Node::Match(m) => {
            collect_free_vars_recursive(&m.subject, bound, vars);
            collect_free_vars_arms(&m.arms, bound, vars);
        }
        Node::For(f) => {
            collect_free_vars_recursive(&f.iterable, bound, vars);
            let mark = bound.len();
            bind_pattern_vars(&f.pattern, bound, vars);
            collect_free_vars_block(&f.body.statements, bound, vars);
            bound.truncate(mark);
        }
        Node::While(w) => {
            let mark = bound.len();
            collect_free_vars_recursive(&w.condition, bound, vars);
            if let Some(p) = &w.let_pattern {
                bind_pattern_vars(p, bound, vars);
            }
            collect_free_vars_block(&w.body.statements, bound, vars);
            bound.truncate(mark);
        }
        Node::Loop(l) => collect_free_vars_block(&l.body.statements, bound, vars),
        Node::Break(b) => {
            if let Some(v) = &b.value {
                collect_free_vars_recursive(v, bound, vars);
            }
        }
        Node::Defer(d) => collect_free_vars_defer(&d.body, bound, vars),
        Node::ErrDefer(d) => collect_free_vars_defer(&d.body, bound, vars),
        Node::Guard(g) => {
            if let Some(c) = &g.condition {
                collect_free_vars_recursive(c, bound, vars);
            }
            collect_free_vars_recursive(&g.result, bound, vars);
        }
        Node::Assert(a) => collect_free_vars_recursive(&a.condition, bound, vars),
        Node::Assume(a) => collect_free_vars_recursive(&a.condition, bound, vars),
        Node::Admit(a) => collect_free_vars_recursive(&a.condition, bound, vars),
        Node::Calc(c) => {
            for step in &c.steps {
                collect_free_vars_recursive(&step.expr, bound, vars);
            }
        }
        Node::Context(c) => {
            collect_free_vars_recursive(&c.context, bound, vars);
            collect_free_vars_block(&c.body.statements, bound, vars);
        }
        Node::With(w) => {
            collect_free_vars_recursive(&w.resource, bound, vars);
            let mark = bound.len();
            if let Some(n) = &w.name {
                bound.push(n.clone());
            }
            collect_free_vars_block(&w.body.statements, bound, vars);
            bound.truncate(mark);
        }
        Node::Function(f) => {
            let mark = bound.len();
            for p in &f.params {
                if let Some(default) = &p.default {
                    collect_free_vars_recursive(default, bound, vars);
                }
            }
            for p in &f.params {
                bound.push(p.name.clone());
            }
            collect_free_vars_block(&f.body.statements, bound, vars);
            bound.truncate(mark);
        }
        // Type/module declarations and no-op statements contribute no reads.
        _ => {}
    }
}

/// Recursively walk the expression tree and collect free identifier names.
fn collect_free_vars_recursive(expr: &Expr, bound: &mut Vec<String>, vars: &mut HashSet<String>) {
    match expr {
        Expr::Identifier(name) => {
            note_free_var(name, bound, vars);
        }
        Expr::Binary { left, right, .. } => {
            collect_free_vars_recursive(left, bound, vars);
            collect_free_vars_recursive(right, bound, vars);
        }
        Expr::Unary { operand, .. } => {
            collect_free_vars_recursive(operand, bound, vars);
        }
        Expr::Call { callee, args } => {
            collect_free_vars_recursive(callee, bound, vars);
            for arg in args {
                collect_free_vars_recursive(&arg.value, bound, vars);
            }
        }
        Expr::KernelLaunch {
            kernel,
            grid,
            block,
            args,
        } => {
            collect_free_vars_recursive(kernel, bound, vars);
            collect_free_vars_recursive(grid, bound, vars);
            collect_free_vars_recursive(block, bound, vars);
            for arg in args {
                collect_free_vars_recursive(&arg.value, bound, vars);
            }
        }
        Expr::MethodCall { receiver, args, .. } | Expr::OptionalMethodCall { receiver, args, .. } => {
            collect_free_vars_recursive(receiver, bound, vars);
            for arg in args {
                collect_free_vars_recursive(&arg.value, bound, vars);
            }
        }
        Expr::FieldAccess { receiver, .. } | Expr::TupleIndex { receiver, .. } => {
            collect_free_vars_recursive(receiver, bound, vars);
        }
        Expr::Index { receiver, index } => {
            collect_free_vars_recursive(receiver, bound, vars);
            collect_free_vars_recursive(index, bound, vars);
        }
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => {
            collect_free_vars_recursive(receiver, bound, vars);
            for part in [start, end, step].into_iter().flatten() {
                collect_free_vars_recursive(part, bound, vars);
            }
        }
        Expr::Tuple(exprs) | Expr::Array(exprs) | Expr::VecLiteral(exprs) => {
            for e in exprs {
                collect_free_vars_recursive(e, bound, vars);
            }
        }
        Expr::LabeledTuple(fields) => {
            for field in fields {
                collect_free_vars_recursive(&field.value, bound, vars);
            }
        }
        Expr::ArrayRepeat { value, count } => {
            collect_free_vars_recursive(value, bound, vars);
            collect_free_vars_recursive(count, bound, vars);
        }
        Expr::Dict(entries) => {
            for (k, v) in entries {
                collect_free_vars_recursive(k, bound, vars);
                collect_free_vars_recursive(v, bound, vars);
            }
        }
        Expr::ListComprehension {
            expr,
            pattern,
            iterable,
            condition,
        } => {
            collect_free_vars_recursive(iterable, bound, vars);
            let mark = bound.len();
            bind_pattern_vars(pattern, bound, vars);
            collect_free_vars_recursive(expr, bound, vars);
            if let Some(c) = condition {
                collect_free_vars_recursive(c, bound, vars);
            }
            bound.truncate(mark);
        }
        Expr::DictComprehension {
            key,
            value,
            pattern,
            iterable,
            condition,
        } => {
            collect_free_vars_recursive(iterable, bound, vars);
            let mark = bound.len();
            bind_pattern_vars(pattern, bound, vars);
            collect_free_vars_recursive(key, bound, vars);
            collect_free_vars_recursive(value, bound, vars);
            if let Some(c) = condition {
                collect_free_vars_recursive(c, bound, vars);
            }
            bound.truncate(mark);
        }
        Expr::If {
            let_pattern,
            condition,
            then_branch,
            else_branch,
        } => {
            let mark = bound.len();
            collect_free_vars_recursive(condition, bound, vars);
            if let Some(p) = let_pattern {
                bind_pattern_vars(p, bound, vars);
            }
            collect_free_vars_recursive(then_branch, bound, vars);
            bound.truncate(mark);
            if let Some(eb) = else_branch {
                collect_free_vars_recursive(eb, bound, vars);
            }
        }
        Expr::Lambda { params, body, .. } => {
            // Walk into nested lambdas -- their free vars are also our free vars,
            // minus the names their own parameters bind.
            let mark = bound.len();
            for p in params {
                bound.push(p.name.clone());
            }
            collect_free_vars_recursive(body, bound, vars);
            bound.truncate(mark);
        }
        Expr::Go { args, params, body } => {
            for a in args {
                collect_free_vars_recursive(a, bound, vars);
            }
            let mark = bound.len();
            for p in params {
                bound.push(p.clone());
            }
            collect_free_vars_recursive(body, bound, vars);
            bound.truncate(mark);
        }
        Expr::Cast { expr, .. }
        | Expr::CastOrReturn { expr, .. }
        | Expr::New { expr, .. }
        | Expr::ContractOld(expr)
        | Expr::Await(expr)
        | Expr::Try(expr)
        | Expr::ForceUnwrap(expr)
        | Expr::ExistsCheck(expr)
        | Expr::Spread(expr)
        | Expr::DictSpread(expr)
        | Expr::OptionalChain { expr, .. } => {
            collect_free_vars_recursive(expr, bound, vars);
        }
        Expr::UnwrapOr { expr, default }
        | Expr::UnwrapOrReturn { expr, default }
        | Expr::CastOr { expr, default, .. }
        | Expr::Coalesce { expr, default } => {
            collect_free_vars_recursive(expr, bound, vars);
            collect_free_vars_recursive(default, bound, vars);
        }
        Expr::UnwrapElse { expr, fallback_fn } | Expr::CastElse { expr, fallback_fn, .. } => {
            collect_free_vars_recursive(expr, bound, vars);
            collect_free_vars_recursive(fallback_fn, bound, vars);
        }
        Expr::Range { start, end, .. } => {
            for part in [start, end].into_iter().flatten() {
                collect_free_vars_recursive(part, bound, vars);
            }
        }
        Expr::FunctionalUpdate { target, args, .. } => {
            collect_free_vars_recursive(target, bound, vars);
            for arg in args {
                collect_free_vars_recursive(&arg.value, bound, vars);
            }
        }
        Expr::FString { parts, .. } => {
            for part in parts {
                match part {
                    FStringPart::Expr(e) | FStringPart::ExprWithFormat(e, _) => {
                        collect_free_vars_recursive(e, bound, vars);
                    }
                    _ => {}
                }
            }
        }
        Expr::StructInit { fields, spread, .. } => {
            for (_, value) in fields {
                collect_free_vars_recursive(value, bound, vars);
            }
            if let Some(s) = spread {
                collect_free_vars_recursive(s, bound, vars);
            }
        }
        Expr::Yield(Some(v)) => {
            collect_free_vars_recursive(v, bound, vars);
        }
        Expr::Yield(None) => {}
        Expr::Spawn(inner) => {
            collect_free_vars_recursive(inner, bound, vars);
        }
        Expr::Forall { pattern, range, predicate } | Expr::Exists { pattern, range, predicate } => {
            collect_free_vars_recursive(range, bound, vars);
            let mark = bound.len();
            bind_pattern_vars(pattern, bound, vars);
            collect_free_vars_recursive(predicate, bound, vars);
            bound.truncate(mark);
        }
        Expr::Match { subject, arms } => {
            collect_free_vars_recursive(subject, bound, vars);
            collect_free_vars_arms(arms, bound, vars);
        }
        Expr::DoBlock(nodes) | Expr::UnsafeBlock(nodes) => {
            collect_free_vars_block(nodes, bound, vars);
        }
        // Literals and other expressions that don't contain variable references
        _ => {}
    }
}
