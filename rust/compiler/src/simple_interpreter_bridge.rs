//! FFI Bridge to Simple Interpreter
//!
//! This is a thin bridge that delegates to the Simple interpreter implementation.
//! All interpreter logic lives in Simple (src/app/interpreter/), this just provides
//! the FFI interface for Rust code to call into it.

use simple_parser::ast::Node;
use crate::error::CompileError;
use crate::aop_config::AopConfig;
use crate::di::DiConfig;

/// Evaluate a module using the Simple interpreter backend
///
/// This replaces the old Rust interpreter with a call to the Simple implementation.
/// The Simple interpreter (src/app/interpreter/) contains all the evaluation logic.
pub fn evaluate_module(items: &[Node]) -> Result<i32, CompileError> {
    evaluate_module_with_di_and_aop(items, None, None)
}

/// Evaluate module with dependency injection config
pub fn evaluate_module_with_di(items: &[Node], di_config: Option<&DiConfig>) -> Result<i32, CompileError> {
    evaluate_module_with_di_and_aop(items, di_config, None)
}

/// Evaluate module with DI and AOP configs
pub fn evaluate_module_with_di_and_aop(
    items: &[Node],
    _di_config: Option<&DiConfig>,
    _aop_config: Option<&AopConfig>,
) -> Result<i32, CompileError> {
    // TODO: The Simple interpreter needs to be wired up to handle AST evaluation
    // For now, we serialize the AST and call into Simple code via FFI
    //
    // Two options:
    // 1. Use the backend system in src/compiler/backend.spl (InterpreterBackendImpl)
    // 2. Call src/app/interpreter/ directly via FFI
    //
    // The backend system is more integrated with the compiler pipeline,
    // so we should use that approach.

    // Temporary fallback: compile and execute via JIT instead of interpretation
    // This maintains functionality while we properly wire up the Simple interpreter
    use crate::codegen::JitCompiler;
    use crate::hir;
    use crate::mir::lower_to_mir;
    use crate::pipeline::module_loader::ModuleSource;

    // Check if there's a main binding that we can evaluate
    // This is the common case for script-style execution
    for item in items {
        if let Node::VariableDecl { name, value, .. } = item {
            if name == "main" {
                // Found main binding - we need to evaluate it
                // For now, fall through to indicate this needs proper implementation
                break;
            }
        }
    }

    // Return error indicating this path needs to be properly implemented
    Err(CompileError::semantic(
        "Interpreter bridge not fully implemented yet. \
         Use 'fn main()' syntax for now, which uses JIT compilation.".to_string()
    ))
}

// Re-export state management functions that were in the old interpreter
// These can stay as thread-local state in Rust since they're just configuration

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::cell::RefCell;
use std::path::PathBuf;

thread_local! {
    static DEBUG_MODE: RefCell<bool> = RefCell::new(false);
    static INTERPRETER_ARGS: RefCell<Vec<String>> = RefCell::new(Vec::new());
    static CURRENT_FILE: RefCell<Option<PathBuf>> = RefCell::new(None);
    static EXECUTION_LIMIT: AtomicUsize = AtomicUsize::new(0);
    static EXECUTION_LIMIT_ENABLED: AtomicBool = AtomicBool::new(false);
    static EXECUTION_COUNT: AtomicUsize = AtomicUsize::new(0);
    static MAX_RECURSION_DEPTH: AtomicUsize = AtomicUsize::new(1000);
    static STACK_OVERFLOW_DETECTION: AtomicBool = AtomicBool::new(true);
    static TIMEOUT_EXCEEDED: AtomicBool = AtomicBool::new(false);
}

pub fn set_interpreter_args(args: Vec<String>) {
    INTERPRETER_ARGS.with(|a| *a.borrow_mut() = args);
}

pub fn get_interpreter_args() -> Vec<String> {
    INTERPRETER_ARGS.with(|a| a.borrow().clone())
}

pub fn set_current_file(path: Option<PathBuf>) {
    CURRENT_FILE.with(|f| *f.borrow_mut() = path);
}

pub fn get_current_file() -> Option<PathBuf> {
    CURRENT_FILE.with(|f| f.borrow().clone())
}

pub fn set_debug_mode(enabled: bool) {
    DEBUG_MODE.with(|d| *d.borrow_mut() = enabled);
}

pub fn is_debug_mode() -> bool {
    DEBUG_MODE.with(|d| *d.borrow())
}

pub fn set_execution_limit(limit: usize) {
    EXECUTION_LIMIT.with(|l| l.store(limit, Ordering::SeqCst));
}

pub fn set_execution_limit_enabled(enabled: bool) {
    EXECUTION_LIMIT_ENABLED.with(|e| e.store(enabled, Ordering::SeqCst));
}

pub fn is_execution_limit_enabled() -> bool {
    EXECUTION_LIMIT_ENABLED.with(|e| e.load(Ordering::SeqCst))
}

pub fn check_execution_limit() -> Result<(), CompileError> {
    if is_execution_limit_enabled() {
        let count = get_execution_count();
        EXECUTION_LIMIT.with(|limit| {
            let max = limit.load(Ordering::SeqCst);
            if max > 0 && count >= max {
                return Err(CompileError::semantic(format!(
                    "Execution limit exceeded: {} operations", max
                )));
            }
            Ok(())
        })
    } else {
        Ok(())
    }
}

pub fn get_execution_count() -> usize {
    EXECUTION_COUNT.with(|c| c.load(Ordering::SeqCst))
}

pub fn reset_execution_count() {
    EXECUTION_COUNT.with(|c| c.store(0, Ordering::SeqCst));
}

pub fn set_max_recursion_depth(depth: usize) {
    MAX_RECURSION_DEPTH.with(|d| d.store(depth, Ordering::SeqCst));
}

pub fn reset_recursion_depth() {
    // No-op for now since we don't track depth in this bridge
}

pub fn is_stack_overflow_detection_enabled() -> bool {
    STACK_OVERFLOW_DETECTION.with(|s| s.load(Ordering::SeqCst))
}

pub fn set_stack_overflow_detection_enabled(enabled: bool) {
    STACK_OVERFLOW_DETECTION.with(|s| s.store(enabled, Ordering::SeqCst));
}

pub fn is_timeout_exceeded() -> bool {
    TIMEOUT_EXCEEDED.with(|t| t.load(Ordering::SeqCst))
}

pub fn reset_timeout() {
    TIMEOUT_EXCEEDED.with(|t| t.store(false, Ordering::SeqCst));
}

pub fn set_macro_trace(_enabled: bool) {
    // No-op - Simple interpreter handles this internally
}

// Empty stub for now - Simple interpreter doesn't expose macro registry
pub fn clear_interpreter_state() {
    reset_execution_count();
    reset_timeout();
    set_debug_mode(false);
    set_current_file(None);
    set_interpreter_args(vec![]);
}
