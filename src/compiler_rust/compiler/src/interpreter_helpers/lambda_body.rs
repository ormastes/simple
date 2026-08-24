//! Shared "evaluate a lambda BODY" helper.
//!
//! A multi-line lambda body parses to `Expr::DoBlock` (parser
//! `parse_lambda_body`, `parser/src/expressions/helpers.rs`), and evaluating a
//! `DoBlock` as an ordinary expression yields an *unforced*
//! `Value::BlockClosure` (`interpreter/expr/control.rs`) instead of running the
//! statements. Every collection helper that called `evaluate_expr(body, ..)`
//! therefore got a closure object back — always-truthy, never executed — so
//! `filter` kept every element, `map` stored closures, and side effects never
//! happened, all with no diagnostic. See
//! `doc/08_tracking/bug/multiline_lambda_body_unforced_blockclosure_2026-08-21.md`.
//!
//! The fix is one shared entry point rather than a patch per method: force the
//! block against the environment the caller already prepared (so effects land
//! where the author wrote them) and yield its last value (so pure helpers get
//! the predicate's result), and evaluate anything else exactly as before.

use std::collections::HashMap;
use std::sync::Arc;

use crate::error::CompileError;
use crate::value::{Env, Value};
use simple_parser::ast::{Block, ClassDef, Expr, FunctionDef};

use super::super::{evaluate_expr, Control, Enums, ImplMethods};

/// Evaluate a lambda body in `env`, forcing a multi-line (`DoBlock` /
/// `UnsafeBlock`) body instead of reifying it into a `Value::BlockClosure`.
pub(crate) fn eval_lambda_body(
    body: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let nodes = match body {
        Expr::DoBlock(nodes) | Expr::UnsafeBlock(nodes) => nodes,
        _ => return evaluate_expr(body, env, functions, classes, enums, impl_methods),
    };
    let block = Block {
        statements: nodes.clone(),
        ..Default::default()
    };
    let (flow, last_val) =
        crate::interpreter::block_exec::exec_block_fn(&block, env, functions, classes, enums, impl_methods)?;
    match flow {
        // A `return` inside a lambda body must leave the enclosing function,
        // not silently become the body's value. Same early-return channel the
        // if/match expression arms use (interpreter/expr/control.rs).
        Control::Return(v) => Err(CompileError::TryError(Box::new(v))),
        _ => Ok(last_val.unwrap_or(Value::Nil)),
    }
}
