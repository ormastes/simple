// Block execution logic with tail injection support

use std::sync::Arc;
use std::collections::HashMap;
use simple_parser::ast::{Block, ClassDef, Expr, FunctionDef, Node};
use crate::error::CompileError;
use crate::value::{strict_mem_enabled, Env, Value};

/// Check if the watchdog timeout has been exceeded (single atomic load, negligible overhead).
macro_rules! check_timeout {
    () => {
        if crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: crate::interpreter::timeout_limit_secs() });
        }
    };
}
use super::core_types::{Control, Enums, ImplMethods, visit_pattern_binding_names};
use super::node_exec::exec_node;
use super::expr::evaluate_expr;
use super::macros::{enter_block_scope, exit_block_scope};
use super::interpreter_control::{exec_match_expr, exec_if_expr, exec_match_core, exec_if_core};
use super::interpreter_helpers::handle_method_call_with_self_update;

/// Capture the pre-block value (if any) of every name that this block directly
/// declares via `var`/`val` (`Node::Let`), `const`, or `static`.
///
/// The flat `Env` has no block-scope stack, so a `var` redeclared inside a
/// nested block (if/for/while/... body) would otherwise silently overwrite —
/// and leak past — the outer binding of the same name. Recording what each
/// name looked like immediately before this block ran lets the caller restore
/// (or remove) it once the block exits, giving nested blocks real scope. See
/// doc/08_tracking/bug/interpreter_nested_block_var_redeclare_leaks_scope_2026-07-17.md.
///
/// Only *direct* statements of this block are scanned — nested blocks (the
/// bodies of `if`/`for`/`while`/`match`/... statements within it) manage their
/// own scope via their own `exec_block`/`exec_block_fn` call, so recursing
/// into them here would double-handle (and mis-scope) their locals.
pub(crate) fn capture_node_scope_shadows(nodes: &[Node], env: &mut Env) -> Vec<(String, Option<Value>)> {
    let mut shadows = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for stmt in nodes {
        let mut names = Vec::new();
        match stmt {
            Node::Let(let_stmt) => {
                visit_pattern_binding_names(&let_stmt.pattern, &mut |name| names.push(name.to_owned()));
            }
            Node::Const(const_stmt) => names.push(const_stmt.name.clone()),
            Node::Static(static_stmt) => names.push(static_stmt.name.clone()),
            _ => {}
        }
        for name in names {
            // Only the first declaration of a name in this block matters: it
            // reflects the value visible from the enclosing scope before this
            // block started executing.
            if seen.insert(name.clone()) {
                let prior_value = env.get(&name).cloned();
                // The owner write-back below needs BOTH a prior value and a
                // non-local name. Test the prior value first: for the common
                // case (a block-local `val` with no outer binding, e.g. every
                // loop-body iteration) that skips the `global_binding` probe
                // and the `CURRENT_EXEC_MODULE` borrow + owner String clone,
                // both of which are pure reads. Same writes in every case
                // where a write happened before.
                if let Some(value) = prior_value.as_ref() {
                    if !env.is_local(&name) {
                        let target = env.global_binding(&name).or_else(|| {
                            crate::interpreter::CURRENT_EXEC_MODULE
                                .with(|cell| cell.borrow().clone())
                                .map(|owner| (owner, name.clone()))
                        });
                        if let Some((owner, source_name)) = target {
                            crate::interpreter::set_owned_global(&owner, &source_name, value.clone(), false);
                        }
                    }
                }
                shadows.push((name.clone(), prior_value));
                env.enter_block_local(name);
            }
        }
    }
    shadows
}

fn capture_block_scope_shadows(block: &Block, env: &mut Env) -> Vec<(String, Option<Value>)> {
    capture_node_scope_shadows(&block.statements, env)
}

/// Undo the shadowing captured by `capture_block_scope_shadows`: restore each
/// name's pre-block value, or remove it entirely if it did not exist before
/// the block ran (so a block-local `var` never leaks into the caller).
pub(crate) fn restore_block_scope_shadows(shadows: Vec<(String, Option<Value>)>, env: &mut Env) {
    for (name, prior_value) in shadows {
        env.exit_block_local(&name);
        let owner_global = if env.is_local(&name) {
            None
        } else {
            let target = env.global_binding(&name).or_else(|| {
                crate::interpreter::CURRENT_EXEC_MODULE
                    .with(|cell| cell.borrow().clone())
                    .map(|owner| (owner, name.clone()))
            });
            target.and_then(|(owner, source_name)| crate::interpreter::owned_global(&owner, &source_name))
        };
        match (owner_global, prior_value) {
            (Some(value), _) => env.refresh_globals([(name, value)]),
            (None, Some(value)) => {
                env.insert(name, value);
            }
            (None, None) => {
                env.remove(&name);
            }
        }
    }
}

pub(crate) fn exec_block(
    block: &Block,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    // Catch module-init hangs and deep call chains that bypass loop-level checks.
    check_timeout!();

    // Enter block scope for tail injection tracking
    let _scope_depth = enter_block_scope();
    let shadows = capture_block_scope_shadows(block, env);

    for stmt in &block.statements {
        match exec_node(stmt, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            flow @ (Control::Return(_) | Control::Break(..) | Control::Continue(_)) => {
                // Execute pending tail injections before exiting the block
                let tail_blocks = exit_block_scope();
                for tail_block in tail_blocks {
                    exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
                }
                restore_block_scope_shadows(shadows, env);
                return Ok(flow);
            }
        }
    }

    // Execute pending tail injections at normal block exit
    let tail_blocks = exit_block_scope();
    for tail_block in tail_blocks {
        exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
    }

    restore_block_scope_shadows(shadows, env);
    Ok(Control::Next)
}

/// Dirty-only write-back from a cloned block env to its outer env.
/// Three channels, kept distinct on purpose:
/// - names the block actually wrote -> plain caller-visible writes;
/// - names a callee refreshed from the global store -> refresh (NOT writes,
///   or they would be re-published upward as this frame's own mutations);
/// - forwarded owner-qualified updates -> forwarded onward.
/// Copying every shared key instead (the old behavior) replays the clone's
/// stale snapshot over values a deeper call wrote after the clone was taken.
/// Strict-mem (plan M5 §3.2, "poison-on-free"/stale-state defect class):
/// regression lock on the `copy_back_block_writes` invariant — a dirty name
/// with no overlay entry means the write-back is about to replay a
/// stale/absent clone snapshot upward, exactly the bug this function was
/// written to fix (copying every shared key instead of only `dirty_names`
/// once replayed a cloned block env's stale snapshot over values a deeper
/// call had since written). Split out from `copy_back_block_writes` so it
/// can be exercised directly by a sabotage-style unit test without touching
/// the process-global `strict_mem_enabled()` gate (see
/// `value_tests_strict_mem.rs`).
pub(crate) fn assert_dirty_names_invariant(block_env: &Env) {
    if let Some(name) = block_env.check_dirty_names_invariant() {
        panic!(
            "strict-mem: dirty-names invariant violated in copy_back_block_writes: \
             '{name}' is marked dirty but has no overlay entry in the block env \
             (write-back would replay a stale clone snapshot upward)"
        );
    }
}

pub(crate) fn copy_back_block_writes(block_env: &Env, env: &mut Env) {
    env.refresh_scope(crate::interpreter::owned_globals_snapshot());
    // Off-path cost: one bool load (see `strict_mem_enabled()`); the check
    // itself is skipped entirely rather than called-and-short-circuited.
    if strict_mem_enabled() {
        assert_dirty_names_invariant(block_env);
    }
    let dirty: Vec<String> = block_env.dirty_names().cloned().collect();
    for key in dirty {
        if env.contains_key(&key) && !block_env.is_refreshed_global(&key) {
            if let Some(value) = block_env.get(&key) {
                env.insert(key.clone(), value.clone());
            }
        }
    }
    let refreshed: Vec<(String, Value)> = block_env
        .refreshed_global_entries()
        .filter(|(name, _)| env.contains_key(name.as_str()) && !env.is_local(name))
        .map(|(name, value)| (name.clone(), value.clone()))
        .collect();
    env.refresh_globals(refreshed);
    for ((owner, name), value) in block_env.forwarded_globals() {
        env.forward_globals(std::sync::Arc::clone(owner), [(name.clone(), value.clone())]);
    }
}

pub(crate) fn exec_unsafe_block(
    nodes: &[Node],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Control, Option<Value>), CompileError> {
    let mut block_env = env.clone();
    // Dirty-only write-back (see interpreter/expr/control.rs if-closure path):
    // copying every shared key replays stale cloned values over newer writes.
    block_env.clear_dirty();
    let block = Block {
        statements: nodes.to_vec(),
        ..Default::default()
    };
    let result = exec_block_fn(&block, &mut block_env, functions, classes, enums, impl_methods)?;
    copy_back_block_writes(&block_env, env);
    Ok(result)
}

/// Execute a block in a function context, supporting implicit return.
/// If the last statement is an expression, its value is captured and returned.
pub(crate) fn exec_block_fn(
    block: &Block,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Control, Option<Value>), CompileError> {
    // Enter block scope for tail injection tracking
    let _scope_depth = enter_block_scope();
    let shadows = capture_block_scope_shadows(block, env);

    let len = block.statements.len();
    let mut last_expr_value: Option<Value> = None;

    for (i, stmt) in block.statements.iter().enumerate() {
        // For the last statement, if it's an expression, capture its value
        let is_last = i == len - 1;
        if is_last {
            if let Node::Expression(Expr::UnsafeBlock(nodes)) = stmt {
                let (flow, value) = exec_unsafe_block(nodes, env, functions, classes, enums, impl_methods)?;
                match flow {
                    Control::Next => last_expr_value = value,
                    other @ (Control::Return(_) | Control::Break(..) | Control::Continue(_)) => {
                        let tail_blocks = exit_block_scope();
                        for tail_block in tail_blocks {
                            exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
                        }
                        restore_block_scope_shadows(shadows, env);
                        return Ok((other, None));
                    }
                }
                continue;
            }
            if let simple_parser::ast::Node::Expression(expr) = stmt {
                // Evaluate and capture the value for implicit return
                // Use handle_method_call_with_self_update to properly track mutations
                let (val, update) =
                    handle_method_call_with_self_update(expr, env, functions, classes, enums, impl_methods)?;
                if let Some((name, new_self)) = update {
                    env.insert(name, new_self);
                }
                last_expr_value = Some(val);
                continue;
            }
            // Handle match as last statement - capture implicit return from match arm.
            // Use exec_match_core (not exec_match_expr) so that explicit `return` statements
            // inside the arm body propagate up instead of being collapsed into a value.
            if let simple_parser::ast::Node::Match(match_stmt) = stmt {
                let (flow, last_val) = exec_match_core(match_stmt, env, functions, classes, enums, impl_methods)?;
                match flow {
                    Control::Next => {
                        last_expr_value = last_val;
                    }
                    other @ (Control::Return(_) | Control::Break(..) | Control::Continue(_)) => {
                        let tail_blocks = exit_block_scope();
                        for tail_block in tail_blocks {
                            exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
                        }
                        restore_block_scope_shadows(shadows, env);
                        return Ok((other, None));
                    }
                }
                continue;
            }
            // Handle if as last statement - capture implicit return from if/else branches.
            // Use exec_if_core (not exec_if_expr) so that explicit `return` statements
            // inside if branches propagate up instead of being collapsed into a value.
            if let simple_parser::ast::Node::If(if_stmt) = stmt {
                let (flow, val) = exec_if_core(if_stmt, env, functions, classes, enums, impl_methods)?;
                match flow {
                    Control::Next => {
                        last_expr_value = Some(val);
                    }
                    other @ (Control::Return(_) | Control::Break(..) | Control::Continue(_)) => {
                        let tail_blocks = exit_block_scope();
                        for tail_block in tail_blocks {
                            exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
                        }
                        restore_block_scope_shadows(shadows, env);
                        return Ok((other, None));
                    }
                }
                continue;
            }
        }

        match exec_node(stmt, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            flow @ (Control::Return(_) | Control::Break(..) | Control::Continue(_)) => {
                // Execute pending tail injections before exiting the block
                let tail_blocks = exit_block_scope();
                for tail_block in tail_blocks {
                    exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
                }
                restore_block_scope_shadows(shadows, env);
                return Ok((flow, None));
            }
        }
    }

    // Execute pending tail injections at normal block exit
    let tail_blocks = exit_block_scope();
    for tail_block in tail_blocks {
        exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
    }

    restore_block_scope_shadows(shadows, env);
    Ok((Control::Next, last_expr_value))
}
