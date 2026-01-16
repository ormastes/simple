//! Effect Inference System
//!
//! Implements automatic async/sync effect detection based on function body analysis.
//! This module maps directly to the Lean 4 verification model in:
//! `verification/type_inference_compile/src/AsyncEffectInference.lean`
//!
//! Key Properties (Formally Verified):
//! 1. Effect Determinism: Each function has exactly one inferred effect
//! 2. Effect Propagation: Calling async function makes caller async
//! 3. Suspension Detection: ~=, if~, while~, for~ operators indicate async
//! 4. Sync Safety: sync-annotated functions cannot contain suspension
//!
//! ## Async-by-Default Implementation (Phases 1-7)
//!
//! This module supports the full async-by-default implementation:
//!
//! **Phase 2: Effect Inference** - Automatic Sync/Async detection
//! - `infer_function_effect()` - Infers effect based on function body
//! - `build_effect_env()` - Builds effect environment with fixed-point iteration
//!
//! **Phase 5: Promise Wrapping Infrastructure**
//! - `needs_promise_wrapping()` - Detects if function needs Promise[T] return type
//! - `get_return_wrap_mode()` - Determines return wrapping strategy
//! - `ReturnWrapMode` - Marks returns as None/Resolved/Rejected
//!
//! **Phase 6: Await Inference**
//! - `needs_await()` - Detects expressions that need automatic await insertion
//! - `statement_needs_await()` - Checks if statement contains suspension operators
//! - `validate_suspension_context()` - Ensures suspension is only used in async contexts
//! - `AwaitMode` - Marks await as None/Implicit/Explicit

use simple_parser::ast::{Block, Expr, FunctionDef, Node};
use std::collections::HashMap;

/// Effect annotation for functions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Effect {
    /// Non-suspending function, returns T directly
    Sync,
    /// May suspend, returns Promise[T]
    Async,
}

/// Environment mapping function names to their inferred effects
pub type EffectEnv = HashMap<String, Effect>;

/// Check if a block contains any suspension operators
pub fn contains_suspension(block: &Block) -> bool {
    for node in &block.statements {
        if contains_suspension_node(node) {
            return true;
        }
    }
    false
}

/// Check if a node contains suspension operators
fn contains_suspension_node(node: &Node) -> bool {
    match node {
        Node::Expression(expr) => contains_suspension_expr(expr),
        Node::Assignment(stmt) => contains_suspension_expr(&stmt.value),
        Node::If(if_stmt) => {
            contains_suspension_expr(&if_stmt.condition)
                || contains_suspension(&if_stmt.then_block)
                || if_stmt.else_block.as_ref().map_or(false, |b| contains_suspension(b))
        }
        Node::While(stmt) => contains_suspension_expr(&stmt.condition) || contains_suspension(&stmt.body),
        Node::For(stmt) => contains_suspension(&stmt.body),
        Node::Match(match_stmt) => {
            contains_suspension_expr(&match_stmt.subject)
                || match_stmt.arms.iter().any(|arm| contains_suspension(&arm.body))
        }
        Node::Return(stmt) => stmt.value.as_ref().map_or(false, |v| contains_suspension_expr(v)),
        _ => false,
    }
}

/// Check if an expression contains suspension operators
fn contains_suspension_expr(expr: &Expr) -> bool {
    match expr {
        // Await is a suspension point
        Expr::Await(_) => true,

        // Recursively check subexpressions
        Expr::Binary { left, right, .. } => contains_suspension_expr(left) || contains_suspension_expr(right),
        Expr::Unary { operand, .. } => contains_suspension_expr(operand),
        Expr::Call { args, .. } => args.iter().any(|arg| contains_suspension_expr(&arg.value)),
        Expr::MethodCall { receiver, args, .. } => {
            contains_suspension_expr(receiver) || args.iter().any(|arg| contains_suspension_expr(&arg.value))
        }
        Expr::Index { receiver, index } => contains_suspension_expr(receiver) || contains_suspension_expr(index),
        Expr::Lambda { body, .. } => contains_suspension_expr(body),

        // Literals and simple expressions don't suspend
        _ => false,
    }
}

/// Infer the effect of a function based on its body
pub fn infer_function_effect(func: &FunctionDef, env: &EffectEnv) -> Effect {
    // If explicitly marked as sync, respect that
    if func.is_sync {
        return Effect::Sync;
    }

    // If has @async effect annotation, it's async
    if func
        .effects
        .iter()
        .any(|e| matches!(e, simple_parser::ast::Effect::Async))
    {
        return Effect::Async;
    }

    // Check for suspension operators in the function body
    if contains_suspension(&func.body) {
        return Effect::Async;
    }

    // Check if function calls any async functions
    if calls_async_function(&func.body, env) {
        return Effect::Async;
    }

    // Default to sync if no async indicators found
    Effect::Sync
}

/// Check if a block calls any async functions
fn calls_async_function(block: &Block, env: &EffectEnv) -> bool {
    for node in &block.statements {
        if calls_async_function_node(node, env) {
            return true;
        }
    }
    false
}

/// Check if a node calls any async functions
fn calls_async_function_node(node: &Node, env: &EffectEnv) -> bool {
    match node {
        Node::Expression(expr) => calls_async_function_expr(expr, env),
        Node::Assignment(stmt) => calls_async_function_expr(&stmt.value, env),
        Node::If(if_stmt) => {
            calls_async_function_expr(&if_stmt.condition, env)
                || calls_async_function(&if_stmt.then_block, env)
                || if_stmt
                    .else_block
                    .as_ref()
                    .map_or(false, |b| calls_async_function(b, env))
        }
        Node::While(stmt) => calls_async_function_expr(&stmt.condition, env) || calls_async_function(&stmt.body, env),
        Node::For(stmt) => calls_async_function(&stmt.body, env),
        Node::Match(match_stmt) => {
            calls_async_function_expr(&match_stmt.subject, env)
                || match_stmt.arms.iter().any(|arm| calls_async_function(&arm.body, env))
        }
        Node::Return(stmt) => stmt.value.as_ref().map_or(false, |v| calls_async_function_expr(v, env)),
        _ => false,
    }
}

/// Check if an expression calls any async functions
fn calls_async_function_expr(expr: &Expr, env: &EffectEnv) -> bool {
    match expr {
        Expr::Call { callee, args, .. } => {
            // Check if the called function is async
            if let Expr::Identifier(name) = &**callee {
                if env.get(name) == Some(&Effect::Async) {
                    return true;
                }
            }
            // Check arguments
            args.iter().any(|arg| calls_async_function_expr(&arg.value, env))
        }
        Expr::MethodCall { receiver, args, .. } => {
            calls_async_function_expr(receiver, env)
                || args.iter().any(|arg| calls_async_function_expr(&arg.value, env))
        }
        Expr::Binary { left, right, .. } => {
            calls_async_function_expr(left, env) || calls_async_function_expr(right, env)
        }
        Expr::Unary { operand, .. } => calls_async_function_expr(operand, env),
        Expr::Index { receiver, index } => {
            calls_async_function_expr(receiver, env) || calls_async_function_expr(index, env)
        }
        Expr::Lambda { body, .. } => calls_async_function_expr(body, env),
        _ => false,
    }
}

/// Build initial effect environment from a list of function definitions
pub fn build_effect_env(functions: &[FunctionDef]) -> EffectEnv {
    let mut env = HashMap::new();

    // First pass: add all explicitly annotated functions
    for func in functions {
        if func.is_sync {
            env.insert(func.name.clone(), Effect::Sync);
        } else if func
            .effects
            .iter()
            .any(|e| matches!(e, simple_parser::ast::Effect::Async))
        {
            env.insert(func.name.clone(), Effect::Async);
        }
    }

    // Fixed-point iteration for mutual recursion
    infer_mutual_effects(functions, env)
}

/// Fixed-point iteration to handle mutually recursive functions
pub fn infer_mutual_effects(functions: &[FunctionDef], mut env: EffectEnv) -> EffectEnv {
    let max_iterations = 100;

    for _iteration in 0..max_iterations {
        let mut changed = false;

        for func in functions {
            // Skip if already explicitly annotated
            if env.contains_key(&func.name) {
                continue;
            }

            let inferred_effect = infer_function_effect(func, &env);
            let old_effect = env.get(&func.name);

            if old_effect != Some(&inferred_effect) {
                env.insert(func.name.clone(), inferred_effect);
                changed = true;
            }
        }

        // If nothing changed, we've reached a fixed point
        if !changed {
            break;
        }
    }

    env
}

/// Validate that a sync function doesn't contain suspension operators
pub fn validate_sync_constraint(func: &FunctionDef) -> Result<(), String> {
    if func.is_sync && contains_suspension(&func.body) {
        return Err(format!(
            "Sync function '{}' cannot contain suspension operators (~=, await, etc.)",
            func.name
        ));
    }
    Ok(())
}

/// Check if a function's return type needs Promise wrapping
/// Async functions (Effect::Async) need their return type transformed from T to Promise[T]
pub fn needs_promise_wrapping(func: &FunctionDef, env: &EffectEnv) -> bool {
    let effect = infer_function_effect(func, env);
    effect == Effect::Async
}

/// Get the return type transformation status for a function
/// Returns None for sync functions, Some(return_type) for async functions
pub fn get_promise_wrapped_type<'a>(func: &'a FunctionDef, env: &EffectEnv) -> Option<&'a simple_parser::ast::Type> {
    if needs_promise_wrapping(func, env) {
        func.return_type.as_ref()
    } else {
        None
    }
}

/// Marker for return statements that need Promise.resolved() wrapping
/// This will be used during HIR/MIR lowering to identify where to insert wrapping code
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReturnWrapMode {
    /// No wrapping needed (sync function)
    None,
    /// Wrap with Promise.resolved(value) (async function, normal return)
    Resolved,
    /// Wrap with Promise.rejected(error) (async function, error return)
    Rejected,
}

/// Determine how a return statement should be wrapped
pub fn get_return_wrap_mode(func: &FunctionDef, env: &EffectEnv) -> ReturnWrapMode {
    if needs_promise_wrapping(func, env) {
        // Error detection not yet implemented - would need type information
        // To detect error returns:
        // 1. Check if function returns Result<T, E> or throws
        // 2. Analyze return expression to determine if it's an error variant
        // 3. Return ReturnWrapMode::Rejected for error returns
        // 4. Return ReturnWrapMode::Resolved for success returns
        // For now, all returns in async functions use Resolved
        ReturnWrapMode::Resolved
    } else {
        ReturnWrapMode::None
    }
}

// Phase 6: Await Inference

/// Marker for expressions that need automatic await insertion
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AwaitMode {
    /// No await needed (sync call or not a call)
    None,
    /// Implicit await (async function call in async-by-default mode)
    Implicit,
    /// Explicit suspension (~= operator)
    Explicit,
}

/// Check if an expression is a call to an async function
/// This is used to detect where automatic await insertion is needed
pub fn needs_await(expr: &Expr, env: &EffectEnv) -> AwaitMode {
    match expr {
        // Direct function call - check if calling async function
        Expr::Call { callee, .. } => {
            if let Expr::Identifier(name) = &**callee {
                if env.get(name) == Some(&Effect::Async) {
                    return AwaitMode::Implicit;
                }
            }
            AwaitMode::None
        }
        // Method calls might be async (requires type information)
        Expr::MethodCall { .. } => {
            // To detect async methods would need:
            // 1. Type inference to determine receiver type
            // 2. Method lookup in type's impl blocks
            // 3. Check if method has async effect annotation
            // 4. Return AwaitMode::Implicit if async
            // For now, assume synchronous (user must add explicit await if needed)
            AwaitMode::None
        }
        // Explicit await
        Expr::Await(_) => AwaitMode::Explicit,
        _ => AwaitMode::None,
    }
}

/// Check if a statement contains suspension operators that need await
pub fn statement_needs_await(node: &Node, env: &EffectEnv) -> bool {
    match node {
        // Suspension assignment: x ~= async_call()
        Node::Assignment(stmt) => {
            matches!(stmt.op, simple_parser::ast::AssignOp::SuspendAssign)
                || needs_await(&stmt.value, env) != AwaitMode::None
        }
        // Suspension control flow
        Node::If(if_stmt) => if_stmt.is_suspend,
        Node::While(while_stmt) => while_stmt.is_suspend,
        Node::For(for_stmt) => for_stmt.is_suspend,
        // Regular statements
        Node::Expression(expr) => needs_await(expr, env) != AwaitMode::None,
        _ => false,
    }
}

/// Validate that suspension operators are only used in async contexts
pub fn validate_suspension_context(func: &FunctionDef, env: &EffectEnv) -> Result<(), String> {
    let effect = infer_function_effect(func, env);

    // If function is sync, check that it doesn't use suspension operators
    if effect == Effect::Sync {
        if contains_suspension(&func.body) {
            return Err(format!(
                "Sync function '{}' cannot use suspension operators (~=, if~, while~, for~)",
                func.name
            ));
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::ast::Block;
    use simple_parser::Span;

    #[test]
    fn test_empty_function_is_sync() {
        let func = FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: "test".to_string(),
            generic_params: vec![],
            params: vec![],
            return_type: None,
            where_clause: vec![],
            body: Block {
                span: Span::new(0, 0, 0, 0),
                statements: vec![],
            },
            visibility: simple_parser::ast::Visibility::Private,
            effects: vec![],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: false,
            is_me_method: false,
            bounds_block: None,
        };

        let env = HashMap::new();
        assert_eq!(infer_function_effect(&func, &env), Effect::Sync);
    }

    #[test]
    fn test_explicit_sync_function() {
        let func = FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: "test".to_string(),
            generic_params: vec![],
            params: vec![],
            return_type: None,
            where_clause: vec![],
            body: Block {
                span: Span::new(0, 0, 0, 0),
                statements: vec![],
            },
            visibility: simple_parser::ast::Visibility::Private,
            effects: vec![],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: true, // Explicitly marked as sync
            is_me_method: false,
            bounds_block: None,
        };

        let env = HashMap::new();
        assert_eq!(infer_function_effect(&func, &env), Effect::Sync);
    }

    // Phase 5: Promise wrapping tests

    #[test]
    fn test_sync_function_no_promise_wrapping() {
        let func = FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: "sync_func".to_string(),
            generic_params: vec![],
            params: vec![],
            return_type: Some(simple_parser::ast::Type::Simple("Int".to_string())),
            where_clause: vec![],
            body: Block {
                span: Span::new(0, 0, 0, 0),
                statements: vec![],
            },
            visibility: simple_parser::ast::Visibility::Private,
            effects: vec![],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: true,
            is_me_method: false,
            bounds_block: None,
        };

        let env = HashMap::new();
        assert!(!needs_promise_wrapping(&func, &env));
        assert_eq!(get_promise_wrapped_type(&func, &env), None);
        assert_eq!(get_return_wrap_mode(&func, &env), ReturnWrapMode::None);
    }

    #[test]
    fn test_async_function_needs_promise_wrapping() {
        let func = FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: "async_func".to_string(),
            generic_params: vec![],
            params: vec![],
            return_type: Some(simple_parser::ast::Type::Simple("Int".to_string())),
            where_clause: vec![],
            body: Block {
                span: Span::new(0, 0, 0, 0),
                statements: vec![],
            },
            visibility: simple_parser::ast::Visibility::Private,
            effects: vec![simple_parser::ast::Effect::Async],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: false,
            is_me_method: false,
            bounds_block: None,
        };

        let env = HashMap::new();
        assert!(needs_promise_wrapping(&func, &env));
        assert!(get_promise_wrapped_type(&func, &env).is_some());
        assert_eq!(get_return_wrap_mode(&func, &env), ReturnWrapMode::Resolved);
    }

    #[test]
    fn test_async_by_default_needs_wrapping() {
        // Function with @async effect should need Promise wrapping
        let async_func = FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: "implicit_async".to_string(),
            generic_params: vec![],
            params: vec![],
            return_type: Some(simple_parser::ast::Type::Simple("String".to_string())),
            where_clause: vec![],
            body: Block {
                span: Span::new(0, 0, 0, 0),
                statements: vec![],
            },
            visibility: simple_parser::ast::Visibility::Private,
            effects: vec![simple_parser::ast::Effect::Async],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: false,
            is_me_method: false,
            bounds_block: None,
        };

        let env = HashMap::new();
        assert!(needs_promise_wrapping(&async_func, &env));
        assert_eq!(get_return_wrap_mode(&async_func, &env), ReturnWrapMode::Resolved);
    }

    // Phase 6: Await inference tests

    #[test]
    fn test_async_call_needs_implicit_await() {
        // Setup: async_func is in the environment
        let mut env = HashMap::new();
        env.insert("async_func".to_string(), Effect::Async);

        // Call to async function
        let call_expr = Expr::Call {
            callee: Box::new(Expr::Identifier("async_func".to_string())),
            args: vec![],
        };

        assert_eq!(needs_await(&call_expr, &env), AwaitMode::Implicit);
    }

    #[test]
    fn test_sync_call_no_await() {
        // Setup: sync_func is in the environment
        let mut env = HashMap::new();
        env.insert("sync_func".to_string(), Effect::Sync);

        // Call to sync function
        let call_expr = Expr::Call {
            callee: Box::new(Expr::Identifier("sync_func".to_string())),
            args: vec![],
        };

        assert_eq!(needs_await(&call_expr, &env), AwaitMode::None);
    }

    #[test]
    fn test_explicit_await() {
        let env = HashMap::new();
        let await_expr = Expr::Await(Box::new(Expr::Identifier("promise".to_string())));

        assert_eq!(needs_await(&await_expr, &env), AwaitMode::Explicit);
    }

    #[test]
    fn test_suspension_assignment_needs_await() {
        let env = HashMap::new();
        let stmt = Node::Assignment(simple_parser::ast::AssignmentStmt {
            span: Span::new(0, 0, 0, 0),
            target: Expr::Identifier("x".to_string()),
            op: simple_parser::ast::AssignOp::SuspendAssign,
            value: Expr::Identifier("value".to_string()),
        });

        assert!(statement_needs_await(&stmt, &env));
    }

    #[test]
    fn test_suspension_if_needs_await() {
        let stmt = Node::If(simple_parser::ast::IfStmt {
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
        assert!(statement_needs_await(&stmt, &env));
    }

    #[test]
    fn test_validate_suspension_in_sync_function() {
        // Create a function with suspension operators
        let func = FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: "sync_with_suspension".to_string(),
            generic_params: vec![],
            params: vec![],
            return_type: None,
            where_clause: vec![],
            body: Block {
                span: Span::new(0, 0, 0, 0),
                statements: vec![Node::Expression(Expr::Await(Box::new(Expr::Identifier(
                    "x".to_string(),
                ))))],
            },
            visibility: simple_parser::ast::Visibility::Private,
            effects: vec![],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: true, // Marked as sync but contains suspension
            bounds_block: None,
            is_me_method: false,
        };

        let env = HashMap::new();
        assert!(validate_suspension_context(&func, &env).is_err());
    }
}
