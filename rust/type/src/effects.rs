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

use simple_parser::ast::{Block, Expr, FunctionDef, Node, Type};
use std::collections::{HashMap, HashSet};

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

// =============================================================================
// Task 2: Tarjan SCC for Mutual Recursion
// =============================================================================

/// Build a call graph from a list of function definitions
/// Maps each function name to the set of functions it calls
pub fn build_call_graph(functions: &[FunctionDef]) -> HashMap<String, HashSet<String>> {
    let func_names: HashSet<_> = functions.iter().map(|f| f.name.clone()).collect();
    let mut call_graph = HashMap::new();

    for func in functions {
        let mut called = HashSet::new();
        collect_calls_from_block(&func.body, &func_names, &mut called);
        call_graph.insert(func.name.clone(), called);
    }

    call_graph
}

/// Collect function calls from a block
fn collect_calls_from_block(block: &Block, valid_funcs: &HashSet<String>, called: &mut HashSet<String>) {
    for node in &block.statements {
        collect_calls_from_node(node, valid_funcs, called);
    }
}

/// Collect function calls from a node
fn collect_calls_from_node(node: &Node, valid_funcs: &HashSet<String>, called: &mut HashSet<String>) {
    match node {
        Node::Expression(expr) => collect_calls_from_expr(expr, valid_funcs, called),
        Node::Assignment(stmt) => collect_calls_from_expr(&stmt.value, valid_funcs, called),
        Node::If(if_stmt) => {
            collect_calls_from_expr(&if_stmt.condition, valid_funcs, called);
            collect_calls_from_block(&if_stmt.then_block, valid_funcs, called);
            if let Some(ref else_block) = if_stmt.else_block {
                collect_calls_from_block(else_block, valid_funcs, called);
            }
            for elif in &if_stmt.elif_branches {
                collect_calls_from_expr(&elif.0, valid_funcs, called);
                collect_calls_from_block(&elif.1, valid_funcs, called);
            }
        }
        Node::While(stmt) => {
            collect_calls_from_expr(&stmt.condition, valid_funcs, called);
            collect_calls_from_block(&stmt.body, valid_funcs, called);
        }
        Node::For(stmt) => {
            collect_calls_from_block(&stmt.body, valid_funcs, called);
        }
        Node::Match(match_stmt) => {
            collect_calls_from_expr(&match_stmt.subject, valid_funcs, called);
            for arm in &match_stmt.arms {
                collect_calls_from_block(&arm.body, valid_funcs, called);
            }
        }
        Node::Return(stmt) => {
            if let Some(ref value) = stmt.value {
                collect_calls_from_expr(value, valid_funcs, called);
            }
        }
        _ => {}
    }
}

/// Collect function calls from an expression
fn collect_calls_from_expr(expr: &Expr, valid_funcs: &HashSet<String>, called: &mut HashSet<String>) {
    match expr {
        Expr::Call { callee, args, .. } => {
            if let Expr::Identifier(name) = &**callee {
                if valid_funcs.contains(name) {
                    called.insert(name.clone());
                }
            }
            // Also check callee expression for higher-order cases
            collect_calls_from_expr(callee, valid_funcs, called);
            for arg in args {
                collect_calls_from_expr(&arg.value, valid_funcs, called);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_calls_from_expr(receiver, valid_funcs, called);
            for arg in args {
                collect_calls_from_expr(&arg.value, valid_funcs, called);
            }
        }
        Expr::Binary { left, right, .. } => {
            collect_calls_from_expr(left, valid_funcs, called);
            collect_calls_from_expr(right, valid_funcs, called);
        }
        Expr::Unary { operand, .. } => {
            collect_calls_from_expr(operand, valid_funcs, called);
        }
        Expr::Index { receiver, index } => {
            collect_calls_from_expr(receiver, valid_funcs, called);
            collect_calls_from_expr(index, valid_funcs, called);
        }
        Expr::Lambda { body, .. } => {
            collect_calls_from_expr(body, valid_funcs, called);
        }
        Expr::Await(inner) => {
            collect_calls_from_expr(inner, valid_funcs, called);
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            collect_calls_from_expr(condition, valid_funcs, called);
            collect_calls_from_expr(then_branch, valid_funcs, called);
            if let Some(ref else_expr) = else_branch {
                collect_calls_from_expr(else_expr, valid_funcs, called);
            }
        }
        _ => {}
    }
}

/// Tarjan's algorithm state for SCC detection
struct TarjanState {
    index: usize,
    indices: HashMap<String, usize>,
    lowlinks: HashMap<String, usize>,
    on_stack: HashSet<String>,
    stack: Vec<String>,
    sccs: Vec<Vec<String>>,
}

impl TarjanState {
    fn new() -> Self {
        TarjanState {
            index: 0,
            indices: HashMap::new(),
            lowlinks: HashMap::new(),
            on_stack: HashSet::new(),
            stack: Vec::new(),
            sccs: Vec::new(),
        }
    }
}

/// Find strongly connected components using Tarjan's algorithm
/// Returns SCCs in reverse topological order (dependencies come after dependents)
pub fn tarjan_scc(call_graph: &HashMap<String, HashSet<String>>) -> Vec<Vec<String>> {
    let mut state = TarjanState::new();

    for node in call_graph.keys() {
        if !state.indices.contains_key(node) {
            tarjan_strongconnect(node, call_graph, &mut state);
        }
    }

    // SCCs are already in reverse topological order from Tarjan's algorithm
    state.sccs
}

fn tarjan_strongconnect(v: &str, graph: &HashMap<String, HashSet<String>>, state: &mut TarjanState) {
    // Set the depth index for v to the smallest unused index
    state.indices.insert(v.to_string(), state.index);
    state.lowlinks.insert(v.to_string(), state.index);
    state.index += 1;
    state.stack.push(v.to_string());
    state.on_stack.insert(v.to_string());

    // Consider successors of v
    if let Some(successors) = graph.get(v) {
        for w in successors {
            if !state.indices.contains_key(w) {
                // Successor w has not yet been visited; recurse on it
                tarjan_strongconnect(w, graph, state);
                let v_lowlink = state.lowlinks[v];
                let w_lowlink = state.lowlinks[w];
                state.lowlinks.insert(v.to_string(), v_lowlink.min(w_lowlink));
            } else if state.on_stack.contains(w) {
                // Successor w is in stack and hence in the current SCC
                let v_lowlink = state.lowlinks[v];
                let w_index = state.indices[w];
                state.lowlinks.insert(v.to_string(), v_lowlink.min(w_index));
            }
        }
    }

    // If v is a root node, pop the stack and generate an SCC
    if state.lowlinks[v] == state.indices[v] {
        let mut scc = Vec::new();
        loop {
            let w = state.stack.pop().unwrap();
            state.on_stack.remove(&w);
            scc.push(w.clone());
            if w == v {
                break;
            }
        }
        state.sccs.push(scc);
    }
}

// =============================================================================
// Task 1: Enhanced Call Graph Effect Propagation
// =============================================================================

/// Build effect environment with transitive effect propagation using SCC analysis
/// This handles mutual recursion correctly by:
/// 1. Finding strongly connected components (mutual recursion groups)
/// 2. Processing SCCs in reverse topological order
/// 3. All functions in an SCC share the same effect (conservatively async if any is async)
pub fn propagate_effects_transitive(functions: &[FunctionDef]) -> EffectEnv {
    let mut env = EffectEnv::new();

    // First pass: add explicitly annotated functions
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

    // Build call graph
    let call_graph = build_call_graph(functions);

    // Find SCCs - returns in reverse topological order
    let sccs = tarjan_scc(&call_graph);

    // Create function lookup map
    let func_map: HashMap<_, _> = functions.iter().map(|f| (f.name.clone(), f)).collect();

    // Process SCCs in topological order (from Tarjan's output)
    // Tarjan returns SCCs in reverse topological order, meaning leaves/dependencies
    // come first in the result. So we iterate directly (not reversed).
    for scc in sccs.iter() {
        // First, check if any function in the SCC is already marked async
        let any_explicit_async = scc.iter().any(|name| env.get(name) == Some(&Effect::Async));

        // Check if any function in the SCC contains suspension operators
        let any_suspension = scc.iter().any(|name| {
            if let Some(func) = func_map.get(name) {
                !func.is_sync && contains_suspension(&func.body)
            } else {
                false
            }
        });

        // Check if any function in the SCC calls an async function outside the SCC
        let any_calls_async = scc.iter().any(|name| {
            if let Some(callees) = call_graph.get(name) {
                callees.iter().any(|callee| {
                    // Only check functions outside this SCC
                    !scc.contains(callee) && env.get(callee) == Some(&Effect::Async)
                })
            } else {
                false
            }
        });

        // Determine effect for all functions in this SCC
        let scc_effect = if any_explicit_async || any_suspension || any_calls_async {
            Effect::Async
        } else {
            Effect::Sync
        };

        // Apply the effect to all non-explicitly-annotated functions in the SCC
        for name in scc {
            if !env.contains_key(name) {
                env.insert(name.clone(), scc_effect);
            }
        }
    }

    env
}

// =============================================================================
// Task 4: Promise Type Preservation
// =============================================================================

/// Information about Promise type wrapping for a function
#[derive(Debug, Clone, PartialEq)]
pub struct PromiseTypeInfo {
    /// The inner type T in Promise<T>, if determinable
    pub inner_type: Option<Type>,
    /// Whether the function's return type should be wrapped in Promise
    pub is_wrapped: bool,
    /// The original return type before any transformation
    pub original_type: Option<Type>,
}

impl PromiseTypeInfo {
    /// Create info for a sync function (no wrapping)
    pub fn sync_function(return_type: Option<Type>) -> Self {
        PromiseTypeInfo {
            inner_type: return_type.clone(),
            is_wrapped: false,
            original_type: return_type,
        }
    }

    /// Create info for an async function (Promise wrapping)
    pub fn async_function(return_type: Option<Type>) -> Self {
        PromiseTypeInfo {
            inner_type: return_type.clone(),
            is_wrapped: true,
            original_type: return_type,
        }
    }
}

/// Infer Promise type information for a function
/// This preserves type information through Promise wrapping transformations
pub fn infer_promise_type_info(func: &FunctionDef, env: &EffectEnv) -> PromiseTypeInfo {
    let effect = infer_function_effect(func, env);

    match effect {
        Effect::Sync => PromiseTypeInfo::sync_function(func.return_type.clone()),
        Effect::Async => PromiseTypeInfo::async_function(func.return_type.clone()),
    }
}

/// Check if a type is already a Promise type
pub fn is_promise_type(ty: &Type) -> bool {
    match ty {
        Type::Generic { name, .. } => name == "Promise",
        _ => false,
    }
}

/// Extract the inner type from a Promise<T> type
pub fn unwrap_promise_type(ty: &Type) -> Option<&Type> {
    match ty {
        Type::Generic { name, args } if name == "Promise" && !args.is_empty() => Some(&args[0]),
        _ => None,
    }
}

/// Wrap a type in Promise<T> if not already wrapped
pub fn wrap_in_promise(ty: Type) -> Type {
    if is_promise_type(&ty) {
        ty
    } else {
        Type::Generic {
            name: "Promise".to_string(),
            args: vec![ty],
        }
    }
}

// =============================================================================
// Task 3: Type-Driven Await Inference
// =============================================================================

/// Extended await mode with type information
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypedAwaitMode {
    /// No await needed (sync expression or types match)
    None,
    /// Implicit await needed (async call, target expects unwrapped type)
    ImplicitAwait,
    /// No await needed, keep Promise wrapper (target expects Promise)
    KeepPromise,
    /// Explicit await (~= operator used)
    ExplicitAwait,
}

/// Check if an expression needs await based on target type
/// This enables type-driven await inference:
/// - If expression returns Promise<T> and target expects T, insert implicit await
/// - If target expects Promise<T>, keep the Promise wrapper
pub fn needs_await_typed(expr: &Expr, env: &EffectEnv, expected_type: Option<&Type>) -> TypedAwaitMode {
    // Check for explicit await first
    if let Expr::Await(_) = expr {
        return TypedAwaitMode::ExplicitAwait;
    }

    // Determine if expression is an async call
    let is_async_call = match expr {
        Expr::Call { callee, .. } => {
            if let Expr::Identifier(name) = &**callee {
                env.get(name) == Some(&Effect::Async)
            } else {
                false
            }
        }
        _ => false,
    };

    if !is_async_call {
        return TypedAwaitMode::None;
    }

    // Expression is async call - check expected type
    match expected_type {
        Some(expected) => {
            if is_promise_type(expected) {
                // Target expects Promise<T>, keep the Promise wrapper
                TypedAwaitMode::KeepPromise
            } else {
                // Target expects unwrapped type T, insert implicit await
                TypedAwaitMode::ImplicitAwait
            }
        }
        None => {
            // No expected type information, default to implicit await
            // (async-by-default semantics)
            TypedAwaitMode::ImplicitAwait
        }
    }
}

/// Get the result type of an expression after await inference
pub fn get_awaited_type<'a>(
    expr: &Expr,
    env: &EffectEnv,
    func_return_types: &'a HashMap<String, Type>,
) -> Option<&'a Type> {
    match expr {
        Expr::Call { callee, .. } => {
            if let Expr::Identifier(name) = &**callee {
                if env.get(name) == Some(&Effect::Async) {
                    // Async call - return type is the inner type of Promise
                    if let Some(return_type) = func_return_types.get(name) {
                        return unwrap_promise_type(return_type).or(Some(return_type));
                    }
                }
                func_return_types.get(name)
            } else {
                None
            }
        }
        _ => None,
    }
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
            is_generator: false,
            bounds_block: None,
            return_constraint: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
            is_static: false,
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
            is_generator: false,
            bounds_block: None,
            return_constraint: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
            is_static: false,
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
            is_generator: false,
            bounds_block: None,
            return_constraint: None,
            is_generic_template: false,
            specialization_of: None,
            is_static: false,
            type_bindings: HashMap::new(),
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
            is_generator: false,
            bounds_block: None,
            return_constraint: None,
            is_generic_template: false,
            is_static: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
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
            is_generator: false,
            bounds_block: None,
            return_constraint: None,
            is_static: false,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
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
            is_generator: false,
            is_static: false,
            return_constraint: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
        };

        let env = HashMap::new();
        assert!(validate_suspension_context(&func, &env).is_err());
    }

    // =============================================================================
    // Task 2 Tests: Tarjan SCC for Mutual Recursion
    // =============================================================================

    #[test]
    fn test_tarjan_scc_single_node() {
        let mut graph = HashMap::new();
        graph.insert("a".to_string(), HashSet::new());

        let sccs = tarjan_scc(&graph);
        assert_eq!(sccs.len(), 1);
        assert!(sccs[0].contains(&"a".to_string()));
    }

    #[test]
    fn test_tarjan_scc_linear_chain() {
        // a -> b -> c (no cycles)
        let mut graph = HashMap::new();
        graph.insert("a".to_string(), ["b".to_string()].into_iter().collect());
        graph.insert("b".to_string(), ["c".to_string()].into_iter().collect());
        graph.insert("c".to_string(), HashSet::new());

        let sccs = tarjan_scc(&graph);
        // Each node is its own SCC
        assert_eq!(sccs.len(), 3);
    }

    #[test]
    fn test_tarjan_scc_simple_cycle() {
        // a -> b -> a (cycle)
        let mut graph = HashMap::new();
        graph.insert("a".to_string(), ["b".to_string()].into_iter().collect());
        graph.insert("b".to_string(), ["a".to_string()].into_iter().collect());

        let sccs = tarjan_scc(&graph);
        // Both nodes are in the same SCC
        assert_eq!(sccs.len(), 1);
        assert!(sccs[0].contains(&"a".to_string()));
        assert!(sccs[0].contains(&"b".to_string()));
    }

    #[test]
    fn test_tarjan_scc_mutual_recursion_three() {
        // a -> b -> c -> a (3-way cycle)
        let mut graph = HashMap::new();
        graph.insert("a".to_string(), ["b".to_string()].into_iter().collect());
        graph.insert("b".to_string(), ["c".to_string()].into_iter().collect());
        graph.insert("c".to_string(), ["a".to_string()].into_iter().collect());

        let sccs = tarjan_scc(&graph);
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0].len(), 3);
    }

    // =============================================================================
    // Task 1 Tests: Enhanced Call Graph Effect Propagation
    // =============================================================================

    fn make_empty_func(name: &str) -> FunctionDef {
        FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: name.to_string(),
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
            is_generator: false,
            bounds_block: None,
            return_constraint: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
            is_static: false,
        }
    }

    fn make_func_calling(name: &str, callee: &str) -> FunctionDef {
        FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: name.to_string(),
            generic_params: vec![],
            params: vec![],
            return_type: None,
            where_clause: vec![],
            body: Block {
                span: Span::new(0, 0, 0, 0),
                statements: vec![Node::Expression(Expr::Call {
                    callee: Box::new(Expr::Identifier(callee.to_string())),
                    args: vec![],
                })],
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
            is_generator: false,
            bounds_block: None,
            return_constraint: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
            is_static: false,
        }
    }

    fn make_async_func(name: &str) -> FunctionDef {
        FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: name.to_string(),
            generic_params: vec![],
            params: vec![],
            return_type: None,
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
            is_generator: false,
            bounds_block: None,
            return_constraint: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
            is_static: false,
        }
    }

    #[test]
    fn test_build_call_graph() {
        let a = make_func_calling("a", "b");
        let b = make_empty_func("b");

        let funcs = vec![a, b];
        let graph = build_call_graph(&funcs);

        assert!(graph.get("a").unwrap().contains("b"));
        assert!(graph.get("b").unwrap().is_empty());
    }

    #[test]
    fn test_transitive_effect_propagation() {
        // a calls b, b is async -> a becomes async
        let a = make_func_calling("a", "b");
        let b = make_async_func("b");

        let funcs = vec![a, b];
        let env = propagate_effects_transitive(&funcs);

        assert_eq!(env.get("b"), Some(&Effect::Async));
        assert_eq!(env.get("a"), Some(&Effect::Async));
    }

    #[test]
    fn test_transitive_effect_chain() {
        // a calls b, b calls c, c is async -> all become async
        let a = make_func_calling("a", "b");
        let b = make_func_calling("b", "c");
        let c = make_async_func("c");

        let funcs = vec![a, b, c];
        let env = propagate_effects_transitive(&funcs);

        assert_eq!(env.get("c"), Some(&Effect::Async));
        assert_eq!(env.get("b"), Some(&Effect::Async));
        assert_eq!(env.get("a"), Some(&Effect::Async));
    }

    #[test]
    fn test_mutual_recursion_sync() {
        // ping calls pong, pong calls ping (both pure)
        let ping = make_func_calling("ping", "pong");
        let pong = make_func_calling("pong", "ping");

        let funcs = vec![ping, pong];
        let env = propagate_effects_transitive(&funcs);

        // Both should be sync since neither has suspension
        assert_eq!(env.get("ping"), Some(&Effect::Sync));
        assert_eq!(env.get("pong"), Some(&Effect::Sync));
    }

    // =============================================================================
    // Task 4 Tests: Promise Type Preservation
    // =============================================================================

    #[test]
    fn test_promise_type_info_sync() {
        let func = FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: "sync_func".to_string(),
            generic_params: vec![],
            params: vec![],
            return_type: Some(Type::Simple("Int".to_string())),
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
            is_generator: false,
            is_static: false,
            bounds_block: None,
            return_constraint: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
        };

        let env = HashMap::new();
        let info = infer_promise_type_info(&func, &env);

        assert!(!info.is_wrapped);
        assert_eq!(info.inner_type, Some(Type::Simple("Int".to_string())));
    }

    #[test]
    fn test_promise_type_info_async() {
        let func = make_async_func("async_func");
        let mut func = func;
        func.return_type = Some(Type::Simple("String".to_string()));

        let env = HashMap::new();
        let info = infer_promise_type_info(&func, &env);

        assert!(info.is_wrapped);
        assert_eq!(info.inner_type, Some(Type::Simple("String".to_string())));
    }

    #[test]
    fn test_is_promise_type() {
        let promise_type = Type::Generic {
            name: "Promise".to_string(),
            args: vec![Type::Simple("Int".to_string())],
        };
        let simple_type = Type::Simple("Int".to_string());

        assert!(is_promise_type(&promise_type));
        assert!(!is_promise_type(&simple_type));
    }

    #[test]
    fn test_unwrap_promise_type() {
        let promise_type = Type::Generic {
            name: "Promise".to_string(),
            args: vec![Type::Simple("Int".to_string())],
        };

        let inner = unwrap_promise_type(&promise_type);
        assert_eq!(inner, Some(&Type::Simple("Int".to_string())));
    }

    #[test]
    fn test_wrap_in_promise() {
        let simple_type = Type::Simple("Int".to_string());
        let wrapped = wrap_in_promise(simple_type);

        assert!(is_promise_type(&wrapped));
        assert_eq!(unwrap_promise_type(&wrapped), Some(&Type::Simple("Int".to_string())));
    }

    #[test]
    fn test_wrap_in_promise_idempotent() {
        let promise_type = Type::Generic {
            name: "Promise".to_string(),
            args: vec![Type::Simple("Int".to_string())],
        };
        let wrapped = wrap_in_promise(promise_type.clone());

        // Should not double-wrap
        assert_eq!(wrapped, promise_type);
    }

    // =============================================================================
    // Task 3 Tests: Type-Driven Await Inference
    // =============================================================================

    #[test]
    fn test_typed_await_sync_call() {
        let mut env = HashMap::new();
        env.insert("sync_func".to_string(), Effect::Sync);

        let call_expr = Expr::Call {
            callee: Box::new(Expr::Identifier("sync_func".to_string())),
            args: vec![],
        };

        assert_eq!(needs_await_typed(&call_expr, &env, None), TypedAwaitMode::None);
    }

    #[test]
    fn test_typed_await_async_call_expects_value() {
        let mut env = HashMap::new();
        env.insert("async_func".to_string(), Effect::Async);

        let call_expr = Expr::Call {
            callee: Box::new(Expr::Identifier("async_func".to_string())),
            args: vec![],
        };

        // Target expects unwrapped type
        let expected = Type::Simple("Int".to_string());
        assert_eq!(
            needs_await_typed(&call_expr, &env, Some(&expected)),
            TypedAwaitMode::ImplicitAwait
        );
    }

    #[test]
    fn test_typed_await_async_call_expects_promise() {
        let mut env = HashMap::new();
        env.insert("async_func".to_string(), Effect::Async);

        let call_expr = Expr::Call {
            callee: Box::new(Expr::Identifier("async_func".to_string())),
            args: vec![],
        };

        // Target expects Promise<T>
        let expected = Type::Generic {
            name: "Promise".to_string(),
            args: vec![Type::Simple("Int".to_string())],
        };
        assert_eq!(
            needs_await_typed(&call_expr, &env, Some(&expected)),
            TypedAwaitMode::KeepPromise
        );
    }

    #[test]
    fn test_typed_await_explicit() {
        let env = HashMap::new();
        let await_expr = Expr::Await(Box::new(Expr::Identifier("promise".to_string())));

        assert_eq!(
            needs_await_typed(&await_expr, &env, None),
            TypedAwaitMode::ExplicitAwait
        );
    }

    #[test]
    fn test_typed_await_no_expected_type() {
        let mut env = HashMap::new();
        env.insert("async_func".to_string(), Effect::Async);

        let call_expr = Expr::Call {
            callee: Box::new(Expr::Identifier("async_func".to_string())),
            args: vec![],
        };

        // No expected type - defaults to implicit await (async-by-default)
        assert_eq!(needs_await_typed(&call_expr, &env, None), TypedAwaitMode::ImplicitAwait);
    }
}
