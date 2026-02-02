//! Environment/Scope FFI
//!
//! Provides opaque handle-based access to interpreter environments from Simple code.
//! Environments are stored in a thread-local registry and accessed via i64 handles.
//!
//! The Rust interpreter uses `Env = HashMap<String, Value>` for variable bindings.
//! This module wraps that with scope-stack semantics so Simple code can:
//! - Push/pop scopes
//! - Define, get, set variables
//! - Take scope snapshots for closures

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Env, Value};
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};

// ============================================================================
// Handle Registry
// ============================================================================

static NEXT_ENV_HANDLE: AtomicI64 = AtomicI64::new(1);

fn next_handle() -> i64 {
    NEXT_ENV_HANDLE.fetch_add(1, Ordering::Relaxed)
}

/// A scope stack wrapping the flat Env (HashMap<String, Value>).
/// Each scope is a set of variable names defined in that scope,
/// allowing proper cleanup on pop.
struct ScopeStack {
    env: Env,
    scope_vars: Vec<Vec<String>>,
    /// Shadowed values saved when pushing scope
    shadow_stack: Vec<Vec<(String, Option<Value>)>>,
}

impl ScopeStack {
    fn new() -> Self {
        ScopeStack {
            env: HashMap::new(),
            scope_vars: vec![vec![]],
            shadow_stack: vec![vec![]],
        }
    }

    fn from_env(env: Env) -> Self {
        ScopeStack {
            env,
            scope_vars: vec![vec![]],
            shadow_stack: vec![vec![]],
        }
    }

    fn push_scope(&mut self) {
        self.scope_vars.push(vec![]);
        self.shadow_stack.push(vec![]);
    }

    fn pop_scope(&mut self) {
        if let (Some(vars), Some(shadows)) =
            (self.scope_vars.pop(), self.shadow_stack.pop())
        {
            // Remove vars defined in this scope
            for name in &vars {
                self.env.remove(name);
            }
            // Restore shadowed values
            for (name, old_val) in shadows {
                match old_val {
                    Some(v) => { self.env.insert(name, v); }
                    None => { self.env.remove(&name); }
                }
            }
        }
    }

    fn define(&mut self, name: String, value: Value) {
        // Save previous value for shadow restoration
        let prev = self.env.get(&name).cloned();
        if let Some(shadows) = self.shadow_stack.last_mut() {
            shadows.push((name.clone(), prev));
        }
        if let Some(vars) = self.scope_vars.last_mut() {
            vars.push(name.clone());
        }
        self.env.insert(name, value);
    }

    fn get(&self, name: &str) -> Option<&Value> {
        self.env.get(name)
    }

    fn set(&mut self, name: &str, value: Value) -> bool {
        if self.env.contains_key(name) {
            self.env.insert(name.to_string(), value);
            true
        } else {
            false
        }
    }

    fn snapshot(&self) -> Env {
        self.env.clone()
    }
}

thread_local! {
    static ENV_REGISTRY: RefCell<HashMap<i64, ScopeStack>> = RefCell::new(HashMap::new());
}

fn get_handle(args: &[Value], index: usize, name: &str) -> Result<i64, CompileError> {
    args.get(index)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                format!("{} expects argument at index {}", name, index),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()
}

fn get_string_arg(args: &[Value], index: usize, name: &str) -> Result<String, CompileError> {
    match args.get(index) {
        Some(Value::Str(s)) => Ok(s.clone()),
        _ => Err(CompileError::semantic_with_context(
            format!("{} expects string argument at index {}", name, index),
            ErrorContext::new().with_code(codes::TYPE_MISMATCH),
        )),
    }
}

fn invalid_handle(name: &str, handle: i64) -> CompileError {
    CompileError::semantic_with_context(
        format!("{}: invalid env handle {}", name, handle),
        ErrorContext::new().with_code(codes::INVALID_OPERATION),
    )
}

// ============================================================================
// Public API: Register envs from Rust side
// ============================================================================

/// Register an existing Env and return a handle
pub fn register_env(env: Env) -> i64 {
    let handle = next_handle();
    ENV_REGISTRY.with(|r| {
        r.borrow_mut().insert(handle, ScopeStack::from_env(env));
    });
    handle
}

/// Get the underlying Env from a handle (for passing back to Rust interpreter)
pub fn get_env(handle: i64) -> Option<Env> {
    ENV_REGISTRY.with(|r| {
        r.borrow().get(&handle).map(|s| s.snapshot())
    })
}

// ============================================================================
// FFI functions callable from Simple
// ============================================================================

/// Create a new empty environment, returns handle
pub fn rt_env_new(_args: &[Value]) -> Result<Value, CompileError> {
    let handle = next_handle();
    ENV_REGISTRY.with(|r| {
        r.borrow_mut().insert(handle, ScopeStack::new());
    });
    Ok(Value::Int(handle))
}

/// Push a new scope
pub fn rt_env_push_scope(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_env_push_scope")?;
    ENV_REGISTRY.with(|r| {
        let mut reg = r.borrow_mut();
        let stack = reg.get_mut(&handle).ok_or_else(|| invalid_handle("rt_env_push_scope", handle))?;
        stack.push_scope();
        Ok(Value::Nil)
    })
}

/// Pop the current scope
pub fn rt_env_pop_scope(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_env_pop_scope")?;
    ENV_REGISTRY.with(|r| {
        let mut reg = r.borrow_mut();
        let stack = reg.get_mut(&handle).ok_or_else(|| invalid_handle("rt_env_pop_scope", handle))?;
        stack.pop_scope();
        Ok(Value::Nil)
    })
}

/// Define a variable in the current scope: (env_handle, name, value)
/// The value is passed as a Value directly (not as an opaque handle)
pub fn rt_env_define(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_env_define")?;
    let name = get_string_arg(args, 1, "rt_env_define")?;
    let value = args.get(2).cloned().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_env_define expects 3 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;
    ENV_REGISTRY.with(|r| {
        let mut reg = r.borrow_mut();
        let stack = reg.get_mut(&handle).ok_or_else(|| invalid_handle("rt_env_define", handle))?;
        stack.define(name, value);
        Ok(Value::Nil)
    })
}

/// Get a variable value: (env_handle, name) -> Value or Nil
pub fn rt_env_get_var(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_env_get_var")?;
    let name = get_string_arg(args, 1, "rt_env_get_var")?;
    ENV_REGISTRY.with(|r| {
        let reg = r.borrow();
        let stack = reg.get(&handle).ok_or_else(|| invalid_handle("rt_env_get_var", handle))?;
        match stack.get(&name) {
            Some(v) => Ok(v.clone()),
            None => Ok(Value::Nil),
        }
    })
}

/// Set a variable value (must already exist): (env_handle, name, value) -> bool
pub fn rt_env_set_var(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_env_set_var")?;
    let name = get_string_arg(args, 1, "rt_env_set_var")?;
    let value = args.get(2).cloned().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_env_set_var expects 3 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;
    ENV_REGISTRY.with(|r| {
        let mut reg = r.borrow_mut();
        let stack = reg.get_mut(&handle).ok_or_else(|| invalid_handle("rt_env_set_var", handle))?;
        Ok(Value::Bool(stack.set(&name, value)))
    })
}

/// Check if a variable exists: (env_handle, name) -> bool
pub fn rt_env_has_var(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_env_has_var")?;
    let name = get_string_arg(args, 1, "rt_env_has_var")?;
    ENV_REGISTRY.with(|r| {
        let reg = r.borrow();
        let stack = reg.get(&handle).ok_or_else(|| invalid_handle("rt_env_has_var", handle))?;
        Ok(Value::Bool(stack.get(&name).is_some()))
    })
}

/// Take a snapshot of the current environment (for closures): returns new env handle
pub fn rt_env_snapshot(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_env_snapshot")?;
    ENV_REGISTRY.with(|r| {
        let reg = r.borrow();
        let stack = reg.get(&handle).ok_or_else(|| invalid_handle("rt_env_snapshot", handle))?;
        let snapshot = stack.snapshot();
        drop(reg);
        let new_handle = register_env(snapshot);
        Ok(Value::Int(new_handle))
    })
}

/// Get current scope depth: (env_handle) -> i64
pub fn rt_env_scope_depth(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_env_scope_depth")?;
    ENV_REGISTRY.with(|r| {
        let reg = r.borrow();
        let stack = reg.get(&handle).ok_or_else(|| invalid_handle("rt_env_scope_depth", handle))?;
        Ok(Value::Int(stack.scope_vars.len() as i64))
    })
}

/// Free an env handle
pub fn rt_env_free_handle(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_env_free_handle")?;
    ENV_REGISTRY.with(|r| {
        r.borrow_mut().remove(&handle);
    });
    Ok(Value::Nil)
}

/// Get total number of variables in env: (env_handle) -> i64
pub fn rt_env_var_count(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_env_var_count")?;
    ENV_REGISTRY.with(|r| {
        let reg = r.borrow();
        let stack = reg.get(&handle).ok_or_else(|| invalid_handle("rt_env_var_count", handle))?;
        Ok(Value::Int(stack.env.len() as i64))
    })
}

/// List all variable names: (env_handle) -> Array<String>
pub fn rt_env_var_names(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_env_var_names")?;
    ENV_REGISTRY.with(|r| {
        let reg = r.borrow();
        let stack = reg.get(&handle).ok_or_else(|| invalid_handle("rt_env_var_names", handle))?;
        let names: Vec<Value> = stack.env.keys().map(|k| Value::Str(k.clone())).collect();
        Ok(Value::Array(names))
    })
}
