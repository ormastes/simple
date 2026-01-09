//! Integration tests for async-by-default implementation (Phases 1-7)
//!
//! This test suite demonstrates the complete async-by-default system:
//! - Phase 1: sync fn keyword parsing
//! - Phase 2: Effect inference (Sync/Async detection)
//! - Phase 3: Promise[T] type (in stdlib)
//! - Phase 4: Suspension operators (~=, if~, while~, for~)
//! - Phase 5: Promise wrapping infrastructure
//! - Phase 6: Await inference
//! - Phase 7: End-to-end integration

use simple_parser::ast::{AssignOp, Block, Expr, FunctionDef, Node};
use simple_parser::Span;
use simple_type::effects::{
    build_effect_env, get_return_wrap_mode, infer_function_effect, needs_await,
    needs_promise_wrapping, statement_needs_await, validate_suspension_context, AwaitMode, Effect,
    ReturnWrapMode,
};
use std::collections::HashMap;

/// Helper to create a minimal function definition
fn make_function(
    name: &str,
    is_sync: bool,
    has_async_effect: bool,
    body: Vec<Node>,
) -> FunctionDef {
    FunctionDef {
        span: Span::new(0, 0, 0, 0),
        name: name.to_string(),
        generic_params: vec![],
        params: vec![],
        return_type: Some(simple_parser::ast::Type::Simple("Int".to_string())),
        where_clause: vec![],
        body: Block {
            span: Span::new(0, 0, 0, 0),
            statements: body,
        },
        visibility: simple_parser::ast::Visibility::Private,
        effects: if has_async_effect {
            vec![simple_parser::ast::Effect::Async]
        } else {
            vec![]
        },
        decorators: vec![],
        attributes: vec![],
        doc_comment: None,
        contract: None,
        is_abstract: false,
        is_sync,
        bounds_block: None,
    }
}

#[test]
fn test_phase_1_sync_keyword() {
    // Phase 1: sync fn keyword is recognized
    let sync_func = make_function("sync_func", true, false, vec![]);
    assert!(sync_func.is_sync);

    let async_func = make_function("async_func", false, false, vec![]);
    assert!(!async_func.is_sync);
}

#[test]
fn test_phase_2_effect_inference() {
    // Phase 2: Effect inference detects async functions
    let sync_func = make_function("sync_func", true, false, vec![]);
    let async_func = make_function("async_func", false, true, vec![]);

    let env = HashMap::new();
    assert_eq!(infer_function_effect(&sync_func, &env), Effect::Sync);
    assert_eq!(infer_function_effect(&async_func, &env), Effect::Async);
}

#[test]
fn test_phase_2_mutual_recursion() {
    // Phase 2: Fixed-point iteration handles mutual recursion
    // func_a calls func_b, func_b calls func_a
    // func_b has @async, so both should be inferred as async

    let func_a = make_function(
        "func_a",
        false,
        false,
        vec![Node::Expression(Expr::Call {
            callee: Box::new(Expr::Identifier("func_b".to_string())),
            args: vec![],
        })],
    );

    let func_b = make_function(
        "func_b",
        false,
        true,
        vec![Node::Expression(Expr::Call {
            callee: Box::new(Expr::Identifier("func_a".to_string())),
            args: vec![],
        })],
    );

    let env = build_effect_env(&[func_a.clone(), func_b.clone()]);

    assert_eq!(env.get("func_a"), Some(&Effect::Async));
    assert_eq!(env.get("func_b"), Some(&Effect::Async));
}

#[test]
fn test_phase_4_suspension_operators() {
    // Phase 4: Suspension operators are recognized
    let suspension_assign = Node::Assignment(simple_parser::ast::AssignmentStmt {
        span: Span::new(0, 0, 0, 0),
        target: Expr::Identifier("x".to_string()),
        op: AssignOp::SuspendAssign,
        value: Expr::Identifier("value".to_string()),
    });

    let suspension_if = Node::If(simple_parser::ast::IfStmt {
        span: Span::new(0, 0, 0, 0),
        let_pattern: None,
        condition: Expr::Bool(true),
        then_block: Block {
            span: Span::new(0, 0, 0, 0),
            statements: vec![],
        },
        elif_branches: vec![],
        else_block: None,
        is_suspend: true,
    });

    let env = HashMap::new();
    assert!(statement_needs_await(&suspension_assign, &env));
    assert!(statement_needs_await(&suspension_if, &env));
}

#[test]
fn test_phase_5_promise_wrapping() {
    // Phase 5: Promise wrapping infrastructure
    let async_func = make_function("async_func", false, true, vec![]);
    let sync_func = make_function("sync_func", true, false, vec![]);

    let env = HashMap::new();

    // Async function needs Promise wrapping
    assert!(needs_promise_wrapping(&async_func, &env));
    assert_eq!(
        get_return_wrap_mode(&async_func, &env),
        ReturnWrapMode::Resolved
    );

    // Sync function doesn't need Promise wrapping
    assert!(!needs_promise_wrapping(&sync_func, &env));
    assert_eq!(get_return_wrap_mode(&sync_func, &env), ReturnWrapMode::None);
}

#[test]
fn test_phase_6_await_inference() {
    // Phase 6: Await inference detects async calls
    let mut env = HashMap::new();
    env.insert("async_func".to_string(), Effect::Async);
    env.insert("sync_func".to_string(), Effect::Sync);

    let async_call = Expr::Call {
        callee: Box::new(Expr::Identifier("async_func".to_string())),
        args: vec![],
    };

    let sync_call = Expr::Call {
        callee: Box::new(Expr::Identifier("sync_func".to_string())),
        args: vec![],
    };

    // Async call needs implicit await
    assert_eq!(needs_await(&async_call, &env), AwaitMode::Implicit);

    // Sync call doesn't need await
    assert_eq!(needs_await(&sync_call, &env), AwaitMode::None);
}

#[test]
fn test_phase_7_end_to_end_async() {
    // Phase 7: End-to-end integration test
    // Scenario: async function that calls another async function

    // Define two async functions
    let fetch_data = make_function(
        "fetch_data",
        false,
        true,
        vec![Node::Return(simple_parser::ast::ReturnStmt {
            span: Span::new(0, 0, 0, 0),
            value: Some(Expr::Integer(42)),
        })],
    );

    let process_data = make_function(
        "process_data",
        false,
        false,
        vec![Node::Expression(Expr::Call {
            callee: Box::new(Expr::Identifier("fetch_data".to_string())),
            args: vec![],
        })],
    );

    // Build effect environment with fixed-point iteration
    let env = build_effect_env(&[fetch_data.clone(), process_data.clone()]);

    // Both functions should be async
    assert_eq!(env.get("fetch_data"), Some(&Effect::Async));
    assert_eq!(env.get("process_data"), Some(&Effect::Async));

    // Both need Promise wrapping
    assert!(needs_promise_wrapping(&fetch_data, &env));
    assert!(needs_promise_wrapping(&process_data, &env));

    // The call to fetch_data needs implicit await
    let call_expr = Expr::Call {
        callee: Box::new(Expr::Identifier("fetch_data".to_string())),
        args: vec![],
    };
    assert_eq!(needs_await(&call_expr, &env), AwaitMode::Implicit);

    // Validation passes (async function can call async function)
    assert!(validate_suspension_context(&process_data, &env).is_ok());
}

#[test]
fn test_phase_7_sync_async_boundary() {
    // Phase 7: Sync function cannot use suspension operators

    let sync_with_await = make_function(
        "sync_with_await",
        true,
        false,
        vec![Node::Expression(Expr::Await(Box::new(Expr::Identifier(
            "promise".to_string(),
        ))))],
    );

    let env = HashMap::new();

    // Validation should fail
    assert!(validate_suspension_context(&sync_with_await, &env).is_err());
}

#[test]
fn test_phase_7_async_by_default() {
    // Phase 7: Demonstrate async-by-default behavior
    // Functions without 'sync' keyword are async by default if they:
    // 1. Call async functions
    // 2. Use suspension operators
    // 3. Have @async effect

    // Define an explicitly async function
    let async_io = make_function(
        "async_io",
        false,
        true,
        vec![Node::Return(simple_parser::ast::ReturnStmt {
            span: Span::new(0, 0, 0, 0),
            value: Some(Expr::Integer(1)),
        })],
    );

    // Function that calls async function -> inferred as async
    let caller = make_function(
        "caller",
        false,
        false,
        vec![Node::Expression(Expr::Call {
            callee: Box::new(Expr::Identifier("async_io".to_string())),
            args: vec![],
        })],
    );

    // Build environment with both functions
    let env = build_effect_env(&[async_io.clone(), caller.clone()]);

    // async_io should be async
    assert_eq!(env.get("async_io"), Some(&Effect::Async));
    // caller should be inferred as async (calls async function)
    assert_eq!(env.get("caller"), Some(&Effect::Async));

    // Both should need Promise wrapping
    assert!(needs_promise_wrapping(&async_io, &env));
    assert!(needs_promise_wrapping(&caller, &env));
}
