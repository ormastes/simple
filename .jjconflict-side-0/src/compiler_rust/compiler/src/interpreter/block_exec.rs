// Block execution logic with tail injection support

use std::sync::Arc;
use std::collections::HashMap;
use simple_parser::ast::{Block, ClassDef, Expr, FunctionDef, Node};
use crate::error::CompileError;
use crate::value::{Env, Value};

/// Check if the watchdog timeout has been exceeded (single atomic load, negligible overhead).
macro_rules! check_timeout {
    () => {
        if crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
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
fn capture_block_scope_shadows(block: &Block, env: &mut Env) -> Vec<(String, Option<Value>)> {
    let mut shadows = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for stmt in &block.statements {
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
                if !env.is_local(&name) {
                    let owner = crate::interpreter::CURRENT_EXEC_MODULE.with(|cell| cell.borrow().clone());
                    if let (Some(owner), Some(value)) = (owner, prior_value.as_ref()) {
                        crate::interpreter::MODULE_GLOBALS_BY_OWNER.with(|cell| {
                            if let Some(globals) = cell.borrow_mut().get_mut(&owner) {
                                if globals.contains_key(&name) {
                                    globals.insert(name.clone(), value.clone());
                                }
                            }
                        });
                    }
                }
                shadows.push((name.clone(), prior_value));
                env.enter_block_local(name);
            }
        }
    }
    shadows
}

/// Undo the shadowing captured by `capture_block_scope_shadows`: restore each
/// name's pre-block value, or remove it entirely if it did not exist before
/// the block ran (so a block-local `var` never leaks into the caller).
fn restore_block_scope_shadows(shadows: Vec<(String, Option<Value>)>, env: &mut Env) {
    for (name, prior_value) in shadows {
        env.exit_block_local(&name);
        let owner_global = if env.is_local(&name) {
            None
        } else {
            let owner = crate::interpreter::CURRENT_EXEC_MODULE.with(|cell| cell.borrow().clone());
            owner.and_then(|owner| {
                crate::interpreter::MODULE_GLOBALS_BY_OWNER
                    .with(|cell| cell.borrow().get(&owner).and_then(|globals| globals.get(&name).cloned()))
            })
        };
        match owner_global.or(prior_value) {
            Some(value) => {
                env.insert(name, value);
            }
            None => {
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

pub(crate) fn exec_unsafe_block(
    nodes: &[Node],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Control, Option<Value>), CompileError> {
    let mut block_env = env.clone();
    let block = Block {
        statements: nodes.to_vec(),
        ..Default::default()
    };
    let result = exec_block_fn(&block, &mut block_env, functions, classes, enums, impl_methods)?;
    for (key, value) in &block_env {
        if env.contains_key(key) {
            env.insert(key.clone(), value.clone());
        }
    }
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
