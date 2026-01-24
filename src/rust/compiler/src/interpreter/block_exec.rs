// Block execution logic with tail injection support

use std::collections::HashMap;
use simple_parser::ast::{Block, ClassDef, FunctionDef};
use crate::error::CompileError;
use crate::value::{Env, Value};
use super::core_types::{Control, Enums, ImplMethods};
use super::node_exec::exec_node;
use super::expr::evaluate_expr;
use super::macros::{enter_block_scope, exit_block_scope};
use super::interpreter_control::{exec_match_expr, exec_if_expr};

pub(crate) fn exec_block(
    block: &Block,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    // Enter block scope for tail injection tracking
    let _scope_depth = enter_block_scope();

    for stmt in &block.statements {
        match exec_node(stmt, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            flow @ (Control::Return(_) | Control::Break(_) | Control::Continue) => {
                // Execute pending tail injections before exiting the block
                let tail_blocks = exit_block_scope();
                for tail_block in tail_blocks {
                    exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
                }
                return Ok(flow);
            }
        }
    }

    // Execute pending tail injections at normal block exit
    let tail_blocks = exit_block_scope();
    for tail_block in tail_blocks {
        exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
    }

    Ok(Control::Next)
}

/// Execute a block in a function context, supporting implicit return.
/// If the last statement is an expression, its value is captured and returned.
pub(crate) fn exec_block_fn(
    block: &Block,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Control, Option<Value>), CompileError> {
    // Enter block scope for tail injection tracking
    let _scope_depth = enter_block_scope();

    let len = block.statements.len();
    let mut last_expr_value: Option<Value> = None;

    for (i, stmt) in block.statements.iter().enumerate() {
        // For the last statement, if it's an expression, capture its value
        let is_last = i == len - 1;
        if is_last {
            if let simple_parser::ast::Node::Expression(expr) = stmt {
                // Evaluate and capture the value for implicit return
                let val = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
                last_expr_value = Some(val);
                continue;
            }
            // Handle match as last statement - capture implicit return from match arm
            if let simple_parser::ast::Node::Match(match_stmt) = stmt {
                let val = exec_match_expr(match_stmt, env, functions, classes, enums, impl_methods)?;
                last_expr_value = Some(val);
                continue;
            }
            // Handle if as last statement - capture implicit return from if/else branches
            if let simple_parser::ast::Node::If(if_stmt) = stmt {
                let val = exec_if_expr(if_stmt, env, functions, classes, enums, impl_methods)?;
                last_expr_value = Some(val);
                continue;
            }
        }

        match exec_node(stmt, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            flow @ (Control::Return(_) | Control::Break(_) | Control::Continue) => {
                // Execute pending tail injections before exiting the block
                let tail_blocks = exit_block_scope();
                for tail_block in tail_blocks {
                    exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
                }
                return Ok((flow, None));
            }
        }
    }

    // Execute pending tail injections at normal block exit
    let tail_blocks = exit_block_scope();
    for tail_block in tail_blocks {
        exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
    }

    Ok((Control::Next, last_expr_value))
}
