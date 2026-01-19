//! Utility functions (index normalization, slicing, control flow, comprehensions, effects, futures)

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Env, FutureValue, Value};
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef, Pattern};
use std::collections::HashMap;

use super::super::{evaluate_expr, exec_block, exec_function, Control, Enums, ImplMethods};
use super::collections::iter_to_vec;
use super::patterns::bind_pattern;

pub(crate) fn normalize_index(idx: i64, len: i64) -> i64 {
    if idx < 0 {
        (len + idx).max(0)
    } else {
        idx.min(len)
    }
}

/// Slice a collection with Python-style semantics
pub(crate) fn slice_collection<T: Clone>(items: &[T], start: i64, end: i64, step: i64) -> Vec<T> {
    let len = items.len() as i64;

    if step > 0 {
        let mut result = Vec::new();
        let mut i = start;
        while i < end && i < len {
            if i >= 0 {
                result.push(items[i as usize].clone());
            }
            i += step;
        }
        result
    } else {
        // Negative step: go backwards
        let mut result = Vec::new();
        let actual_start = if start == 0 { len - 1 } else { start.min(len - 1) };
        let actual_end = if end == len { -1 } else { end };
        let mut i = actual_start;
        while i > actual_end && i >= 0 {
            if (i as usize) < items.len() {
                result.push(items[i as usize].clone());
            }
            i += step;
        }
        result
    }
}

/// Convert a Control result to a Value result for function return.
/// This is used by multiple interpreter modules to handle function return values.
pub(crate) fn control_to_value(result: Result<Control, CompileError>) -> Result<Value, CompileError> {
    match result {
        Ok(Control::Return(v)) => Ok(v),
        Ok(Control::Next) => Ok(Value::Nil),
        Ok(Control::Break(_)) => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("break can only be used inside a loop");
            Err(CompileError::semantic_with_context(
                "break outside loop".to_string(),
                ctx,
            ))
        }
        Ok(Control::Continue) => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("continue can only be used inside a loop");
            Err(CompileError::semantic_with_context(
                "continue outside loop".to_string(),
                ctx,
            ))
        }
        Err(e) => Err(e),
    }
}

/// Iterate over items with pattern binding and optional condition filtering.
/// Returns a vector of environments for items that match the pattern and pass the condition.
/// This is used by both ListComprehension and DictComprehension to avoid code duplication.
pub(crate) fn comprehension_iterate(
    iterable: &Value,
    pattern: &Pattern,
    condition: &Option<Box<Expr>>,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Vec<Env>, CompileError> {
    let items = iter_to_vec(iterable)?;
    let mut result = Vec::new();

    for item in items {
        // Create a new scope with the pattern binding
        let mut inner_env = env.clone();
        if !bind_pattern(pattern, &item, &mut inner_env) {
            continue;
        }

        // Check condition if present
        if let Some(cond) = condition {
            let cond_val = evaluate_expr(cond, &mut inner_env, functions, classes, enums, impl_methods)?;
            if !cond_val.truthy() {
                continue;
            }
        }

        result.push(inner_env);
    }

    Ok(result)
}

// ============================================================================
// Effect management helpers
// ============================================================================

/// Execute a closure with the given function's effect context.
/// Saves the current effects, sets the function's effects if present,
/// executes the closure, and restores the previous effects.
pub(crate) fn with_effect_context<F, T>(func_effects: &[simple_parser::ast::Effect], f: F) -> T
where
    F: FnOnce() -> T,
{
    use crate::effects::{restore_effects, set_current_effects};

    // Only change context if function has explicit effects
    if func_effects.is_empty() {
        return f();
    }

    let prev_effects = set_current_effects(func_effects);
    let result = f();
    restore_effects(prev_effects);
    result
}

// ============================================================================
// Async execution helpers (reduce duplication in spawn_isolated, async, pool.submit)
// ============================================================================

/// Cloned interpreter context for async execution.
/// Used to pass execution context across thread boundaries.
#[derive(Clone)]
struct ClonedContext {
    functions: HashMap<String, FunctionDef>,
    classes: HashMap<String, ClassDef>,
    enums: Enums,
    impl_methods: ImplMethods,
}

impl ClonedContext {
    /// Clone context from references
    fn from_refs(
        functions: &mut HashMap<String, FunctionDef>,
        classes: &mut HashMap<String, ClassDef>,
        enums: &Enums,
        impl_methods: &ImplMethods,
    ) -> Self {
        Self {
            functions: functions.clone(),
            classes: classes.clone(),
            enums: enums.clone(),
            impl_methods: impl_methods.clone(),
        }
    }
}

/// Execute a callable (Function or Lambda) with a single argument.
/// If base_env is provided, it's used as the base environment (for spawn_isolated).
/// Otherwise, the callable's captured_env is used (for pool.submit).
/// Returns Ok(value) or Err(error_message).
fn execute_callable_with_arg(
    callable: Value,
    arg: Value,
    base_env: Option<&Env>,
    ctx: &mut ClonedContext,
) -> Result<Value, String> {
    match callable {
        Value::Function {
            ref def,
            ref captured_env,
            ..
        } => {
            // Use base_env if provided (spawn_isolated), otherwise use captured_env (pool.submit)
            let mut local_env = base_env.cloned().unwrap_or_else(|| captured_env.clone());
            if let Some(first_param) = def.params.first() {
                local_env.insert(first_param.name.clone(), arg);
            }
            match exec_block(
                &def.body,
                &mut local_env,
                &mut ctx.functions,
                &mut ctx.classes,
                &ctx.enums,
                &ctx.impl_methods,
            ) {
                Ok(Control::Return(v)) => Ok(v),
                Ok(_) => Ok(Value::Nil),
                Err(e) => Err(format!("{:?}", e)),
            }
        }
        Value::Lambda {
            ref params,
            ref body,
            ref env,
        } => {
            // For lambdas, always use the captured env (they are closures)
            let mut local_env = env.clone();
            if let Some(first_param) = params.first() {
                local_env.insert(first_param.clone(), arg);
            }
            evaluate_expr(
                &body,
                &mut local_env,
                &mut ctx.functions,
                &mut ctx.classes,
                &ctx.enums,
                &ctx.impl_methods,
            )
            .map_err(|e| format!("{:?}", e))
        }
        _ => Err("expected a function or lambda".into()),
    }
}

/// Create a FutureValue that executes a callable with an argument.
/// Uses the callable's captured environment.
/// Clones all necessary context for thread-safe execution.
pub(crate) fn spawn_future_with_callable(
    callable: Value,
    arg: Value,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> FutureValue {
    let mut ctx = ClonedContext::from_refs(functions, classes, enums, impl_methods);
    FutureValue::new(move || execute_callable_with_arg(callable, arg, None, &mut ctx))
}

/// Create a FutureValue that executes a callable with an argument and outer environment.
/// Uses the outer environment as the base (for spawn_isolated semantics).
/// Clones all necessary context for thread-safe execution.
pub(crate) fn spawn_future_with_callable_and_env(
    callable: Value,
    arg: Value,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> FutureValue {
    let mut env_clone = env.clone();
    let mut ctx = ClonedContext::from_refs(functions, classes, enums, impl_methods);
    FutureValue::new(move || execute_callable_with_arg(callable, arg, Some(&env_clone), &mut ctx))
}

/// Create a FutureValue that evaluates an expression.
/// Clones all necessary context for thread-safe execution.
pub(crate) fn spawn_future_with_expr(
    expr: Expr,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> FutureValue {
    let mut env_clone = env.clone();
    let mut ctx = ClonedContext::from_refs(functions, classes, enums, impl_methods);
    FutureValue::new(move || {
        evaluate_expr(
            &expr,
            &mut env_clone,
            &mut ctx.functions,
            &mut ctx.classes,
            &ctx.enums,
            &ctx.impl_methods,
        )
        .map_err(|e| format!("{:?}", e))
    })
}
