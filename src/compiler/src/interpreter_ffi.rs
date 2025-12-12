//! FFI interface for the interpreter.
//!
//! This module provides C-compatible entry points for calling the interpreter
//! from compiled code. It enables the hybrid execution model where compiled
//! code can fall back to the interpreter for unsupported features.

use std::cell::RefCell;
use std::collections::HashMap;
use std::ffi::{c_char, CStr};
use std::sync::RwLock;

use simple_parser::ast::{ClassDef, Expr, FunctionDef, Node, Visibility};
use simple_parser::token::Span;

use crate::error::CompileError;
use crate::interpreter::{evaluate_expr, evaluate_module, exec_block, control_to_value, Enums, ImplMethods};
use crate::value::{Env, Value};
use crate::value_bridge::BridgeValue;

// ============================================================================
// Thread-local interpreter state
// ============================================================================

thread_local! {
    /// Environment for interpreted code
    static INTERP_ENV: RefCell<Env> = RefCell::new(HashMap::new());

    /// Function definitions
    static INTERP_FUNCTIONS: RefCell<HashMap<String, FunctionDef>> = RefCell::new(HashMap::new());

    /// Class definitions
    static INTERP_CLASSES: RefCell<HashMap<String, ClassDef>> = RefCell::new(HashMap::new());

    /// Enum definitions
    static INTERP_ENUMS: RefCell<Enums> = RefCell::new(HashMap::new());

    /// Impl block methods
    static INTERP_IMPL_METHODS: RefCell<ImplMethods> = RefCell::new(HashMap::new());
}

// ============================================================================
// Global registry for compiled functions
// ============================================================================

/// Signature of a compiled function
#[derive(Clone)]
pub struct CompiledFnSignature {
    /// Number of parameters
    pub param_count: usize,
    /// Whether the function returns a value
    pub has_return: bool,
}

/// A compiled function entry
pub struct CompiledFn {
    /// Pointer to the compiled function
    pub ptr: *const u8,
    /// Function signature
    pub signature: CompiledFnSignature,
}

// Safety: We manage the lifetime of compiled function pointers carefully
unsafe impl Send for CompiledFn {}
unsafe impl Sync for CompiledFn {}

lazy_static::lazy_static! {
    /// Registry of compiled functions accessible from the interpreter
    static ref COMPILED_FUNCTIONS: RwLock<HashMap<String, CompiledFn>> = RwLock::new(HashMap::new());
}

/// Register a compiled function for interpreter access
pub fn register_compiled_fn(name: &str, ptr: *const u8, signature: CompiledFnSignature) {
    COMPILED_FUNCTIONS
        .write()
        .unwrap()
        .insert(name.to_string(), CompiledFn { ptr, signature });
}

/// Unregister a compiled function
pub fn unregister_compiled_fn(name: &str) {
    COMPILED_FUNCTIONS.write().unwrap().remove(name);
}

/// Check if a function is compiled
pub fn is_function_compiled(name: &str) -> bool {
    COMPILED_FUNCTIONS.read().unwrap().contains_key(name)
}

// ============================================================================
// Interpreter initialization
// ============================================================================

/// Initialize the interpreter with a module's AST.
///
/// This extracts function definitions, class definitions, etc. from the AST
/// and stores them in thread-local storage for later use.
pub fn init_interpreter_state(items: &[Node]) {
    INTERP_FUNCTIONS.with(|funcs| {
        let mut funcs = funcs.borrow_mut();
        funcs.clear();
        for item in items {
            if let Node::Function(f) = item {
                funcs.insert(f.name.clone(), f.clone());
            }
        }
    });

    INTERP_CLASSES.with(|classes| {
        let mut classes = classes.borrow_mut();
        classes.clear();
        for item in items {
            if let Node::Class(c) = item {
                classes.insert(c.name.clone(), c.clone());
            } else if let Node::Struct(s) = item {
                // Struct is treated as class for now
                classes.insert(
                    s.name.clone(),
                    ClassDef {
                        span: Span::new(0, 0, 0, 0),
                        name: s.name.clone(),
                        generic_params: s.generic_params.clone(),
                        fields: s.fields.clone(),
                        methods: vec![],
                        parent: None,
                        visibility: Visibility::Public,
                        attributes: vec![],
                        doc_comment: None,
                    },
                );
            }
        }
    });

    INTERP_ENUMS.with(|enums| {
        let mut enums = enums.borrow_mut();
        enums.clear();
        for item in items {
            if let Node::Enum(e) = item {
                enums.insert(e.name.clone(), e.clone());
            }
        }
    });

    INTERP_IMPL_METHODS.with(|impl_methods| {
        let mut impl_methods = impl_methods.borrow_mut();
        impl_methods.clear();
        for item in items {
            if let Node::Impl(impl_block) = item {
                // Extract type name from the target_type
                let type_name = format!("{:?}", impl_block.target_type);
                let methods = impl_methods.entry(type_name).or_insert_with(Vec::new);
                methods.extend(impl_block.methods.clone());
            }
        }
    });

    INTERP_ENV.with(|env| {
        env.borrow_mut().clear();
    });
}

/// Clear interpreter state
pub fn clear_interpreter_state() {
    INTERP_FUNCTIONS.with(|f| f.borrow_mut().clear());
    INTERP_CLASSES.with(|c| c.borrow_mut().clear());
    INTERP_ENUMS.with(|e| e.borrow_mut().clear());
    INTERP_IMPL_METHODS.with(|i| i.borrow_mut().clear());
    INTERP_ENV.with(|e| e.borrow_mut().clear());
}

// ============================================================================
// Helper to access all thread-local state
// ============================================================================

/// Execute a closure with access to all interpreter thread-local state.
/// This eliminates the deeply nested `.with()` calls throughout the module.
fn with_interp_state<F, R>(f: F) -> R
where
    F: FnOnce(
        &Env,
        &HashMap<String, FunctionDef>,
        &HashMap<String, ClassDef>,
        &Enums,
        &ImplMethods,
    ) -> R,
{
    INTERP_ENV.with(|env| {
        let env = env.borrow();
        INTERP_FUNCTIONS.with(|funcs| {
            let funcs = funcs.borrow();
            INTERP_CLASSES.with(|classes| {
                let classes = classes.borrow();
                INTERP_ENUMS.with(|enums| {
                    let enums = enums.borrow();
                    INTERP_IMPL_METHODS.with(|impl_methods| {
                        let impl_methods = impl_methods.borrow();
                        f(&env, &funcs, &classes, &enums, &impl_methods)
                    })
                })
            })
        })
    })
}

// ============================================================================
// FFI entry points
// ============================================================================

/// Initialize interpreter state from AST (FFI-safe wrapper).
///
/// # Safety
/// The `items_ptr` must point to a valid slice of `Node` items.
#[no_mangle]
pub unsafe extern "C" fn simple_interp_init(items_ptr: *const Node, items_len: usize) {
    if items_ptr.is_null() {
        return;
    }
    let items = std::slice::from_raw_parts(items_ptr, items_len);
    init_interpreter_state(items);
}

/// Call an interpreted function from compiled code.
///
/// # Arguments
/// * `func_name` - Null-terminated function name
/// * `argc` - Number of arguments
/// * `argv` - Array of BridgeValue pointers
///
/// # Returns
/// BridgeValue containing the result (or error)
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn simple_interp_call(
    func_name: *const c_char,
    argc: usize,
    argv: *const BridgeValue,
) -> BridgeValue {
    // Parse function name
    if func_name.is_null() {
        return BridgeValue::error("null function name");
    }
    let name = match CStr::from_ptr(func_name).to_str() {
        Ok(s) => s,
        Err(_) => return BridgeValue::error("invalid function name encoding"),
    };

    // Convert arguments
    let args: Vec<Value> = if argc > 0 && !argv.is_null() {
        let arg_slice = std::slice::from_raw_parts(argv, argc);
        arg_slice.iter().map(|bv| bv.to_value()).collect()
    } else {
        vec![]
    };

    // Look up and call the function
    let result = with_interp_state(|env, funcs, classes, enums, impl_methods| {
        if let Some(func) = funcs.get(name) {
            call_interpreted_function(func, args.clone(), env, funcs, classes, enums, impl_methods)
        } else {
            Err(CompileError::Semantic(format!("function not found: {}", name)))
        }
    });

    match result {
        Ok(value) => BridgeValue::from(&value),
        Err(e) => BridgeValue::error(&format!("{:?}", e)),
    }
}

/// Call an interpreted function with the given arguments.
fn call_interpreted_function(
    func: &FunctionDef,
    args: Vec<Value>,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Build local environment with arguments bound to parameters
    let mut local_env = env.clone();
    for (i, param) in func.params.iter().enumerate() {
        if let Some(arg) = args.get(i) {
            local_env.insert(param.name.clone(), arg.clone());
        } else if let Some(default) = &param.default {
            // Use default value if not provided
            let default_val =
                evaluate_expr(default, &local_env, functions, classes, enums, impl_methods)?;
            local_env.insert(param.name.clone(), default_val);
        }
    }

    // Execute the function body
    let result = exec_block(
        &func.body,
        &mut local_env,
        functions,
        classes,
        enums,
        impl_methods,
    );
    control_to_value(result)
}

/// Evaluate a single expression via the interpreter.
///
/// # Safety
/// The `expr_ptr` must point to a valid `Expr`.
#[no_mangle]
pub unsafe extern "C" fn simple_interp_eval_expr(expr_ptr: *const Expr) -> BridgeValue {
    if expr_ptr.is_null() {
        return BridgeValue::error("null expression");
    }
    let expr = &*expr_ptr;

    let result = with_interp_state(|env, funcs, classes, enums, impl_methods| {
        evaluate_expr(expr, env, funcs, classes, enums, impl_methods)
    });

    match result {
        Ok(value) => BridgeValue::from(&value),
        Err(e) => BridgeValue::error(&format!("{:?}", e)),
    }
}

/// Run a complete module through the interpreter.
///
/// # Safety
/// The `items_ptr` must point to a valid slice of `Node` items.
#[no_mangle]
pub unsafe extern "C" fn simple_interp_run_module(items_ptr: *const Node, items_len: usize) -> i32 {
    if items_ptr.is_null() {
        return -1;
    }
    let items = std::slice::from_raw_parts(items_ptr, items_len);

    match evaluate_module(items) {
        Ok(exit_code) => exit_code,
        Err(_) => -1,
    }
}

/// Set a variable in the interpreter environment.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn simple_interp_set_var(name: *const c_char, value: BridgeValue) -> bool {
    if name.is_null() {
        return false;
    }
    let name_str = match CStr::from_ptr(name).to_str() {
        Ok(s) => s.to_string(),
        Err(_) => return false,
    };

    let val = value.to_value();
    INTERP_ENV.with(|env| {
        env.borrow_mut().insert(name_str, val);
    });
    true
}

/// Get a variable from the interpreter environment.
///
/// # Safety
/// The `name` pointer must be valid.
#[no_mangle]
pub unsafe extern "C" fn simple_interp_get_var(name: *const c_char) -> BridgeValue {
    if name.is_null() {
        return BridgeValue::nil();
    }
    let name_str = match CStr::from_ptr(name).to_str() {
        Ok(s) => s,
        Err(_) => return BridgeValue::nil(),
    };

    INTERP_ENV.with(|env| {
        let env = env.borrow();
        if let Some(value) = env.get(name_str) {
            BridgeValue::from(value)
        } else {
            BridgeValue::nil()
        }
    })
}

// ============================================================================
// Rust-friendly API (for use within the compiler)
// ============================================================================

/// Call an interpreted function by name with Value arguments.
pub fn call_interp_function(name: &str, args: Vec<Value>) -> Result<Value, CompileError> {
    with_interp_state(|env, funcs, classes, enums, impl_methods| {
        if let Some(func) = funcs.get(name) {
            call_interpreted_function(func, args, env, funcs, classes, enums, impl_methods)
        } else {
            Err(CompileError::Semantic(format!("function not found: {}", name)))
        }
    })
}

/// Evaluate an expression using interpreter state.
pub fn eval_expr_with_state(expr: &Expr) -> Result<Value, CompileError> {
    with_interp_state(|env, funcs, classes, enums, impl_methods| {
        evaluate_expr(expr, env, funcs, classes, enums, impl_methods)
    })
}

/// Set a variable in the interpreter environment (Rust API).
pub fn set_interp_var(name: &str, value: Value) {
    INTERP_ENV.with(|env| {
        env.borrow_mut().insert(name.to_string(), value);
    });
}

/// Get a variable from the interpreter environment (Rust API).
pub fn get_interp_var(name: &str) -> Option<Value> {
    INTERP_ENV.with(|env| env.borrow().get(name).cloned())
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init_clear_state() {
        init_interpreter_state(&[]);
        INTERP_FUNCTIONS.with(|f| assert!(f.borrow().is_empty()));

        clear_interpreter_state();
        INTERP_ENV.with(|e| assert!(e.borrow().is_empty()));
    }

    #[test]
    fn test_set_get_var() {
        clear_interpreter_state();

        set_interp_var("x", Value::Int(42));
        let val = get_interp_var("x");
        assert_eq!(val, Some(Value::Int(42)));

        let missing = get_interp_var("missing");
        assert_eq!(missing, None);
    }

    #[test]
    fn test_compiled_fn_registry() {
        let sig = CompiledFnSignature {
            param_count: 1,
            has_return: true,
        };

        register_compiled_fn("test_fn", std::ptr::null(), sig);
        assert!(is_function_compiled("test_fn"));

        unregister_compiled_fn("test_fn");
        assert!(!is_function_compiled("test_fn"));
    }
}
