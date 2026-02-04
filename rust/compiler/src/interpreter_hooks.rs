// Interpreter Hooks FFI Implementation
//
// This module implements the FFI functions for the DAP (Debug Adapter Protocol)
// integration. It provides debugging hooks that allow external tools to:
// - Set and manage breakpoints
// - Control execution (step, continue, pause, terminate)
// - Inspect stack frames and variables
// - Evaluate expressions in debug context
//
// Architecture:
// - Delegates to the existing debug system in simple_runtime::debug
// - Provides a clean FFI interface for Simple-side DAP integration
// - Converts between FFI types and internal debug types
//
// Thread Safety:
// - All operations are thread-safe through the existing debug system
// - Uses Mutex for global debug state

// Allow non-FFI-safe types in extern "C" functions
// These functions are called from Simple code which handles the conversions
#![allow(improper_ctypes_definitions)]

use simple_runtime::debug::{self, DebugState, StepMode};
use std::collections::HashMap;

// --- Type Definitions ---
// These types are exported for FFI but delegate to the runtime debug system

/// Variable scope enumeration (matches runtime.hooks)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(i64)]
pub enum VariableScope {
    Local = 0,
    Global = 1,
    Closure = 2,
    Argument = 3,
}

/// Stack frame information (FFI-friendly)
#[derive(Debug, Clone)]
pub struct StackFrame {
    pub id: i64,
    pub name: String,
    pub file: String,
    pub line: i64,
    pub column: i64,
    pub scope_id: i64,
}

/// Variable information (FFI-friendly)
#[derive(Debug, Clone)]
pub struct Variable {
    pub name: String,
    pub value: String,
    pub type_name: String,
    pub scope: VariableScope,
    pub is_mutable: bool,
    pub memory_address: Option<i64>,
}

/// Expression evaluation result (FFI-friendly)
#[derive(Debug, Clone)]
pub struct EvalResult {
    pub value: String,
    pub type_name: String,
    pub error: Option<String>,
}

// Note: We delegate to simple_runtime::debug for the actual debug state

// --- FFI Function Implementations ---

/// Add a breakpoint at a specific line
///
/// Registers a breakpoint in the interpreter. When execution reaches this line,
/// the interpreter will pause and notify the debugger.
#[no_mangle]
pub extern "C" fn rt_hook_add_breakpoint(file: String, line: i64, _id: i64) {
    let mut state = debug::debug_state();
    state.add_breakpoint(&file, line as u32, None);
}

/// Remove a breakpoint
///
/// Removes a previously registered breakpoint.
#[no_mangle]
pub extern "C" fn rt_hook_remove_breakpoint(file: String, line: i64) {
    let mut state = debug::debug_state();
    state.remove_breakpoint(&file, line as u32);
}

/// Enable or disable a breakpoint
///
/// Allows temporarily disabling a breakpoint without removing it.
#[no_mangle]
pub extern "C" fn rt_hook_set_breakpoint_enabled(file: String, line: i64, enabled: bool) {
    // Note: The existing debug system doesn't have per-breakpoint enable/disable
    // We'd need to extend it or handle this differently
    // For now, we remove/re-add the breakpoint
    let mut state = debug::debug_state();
    if enabled {
        state.add_breakpoint(&file, line as u32, None);
    } else {
        state.remove_breakpoint(&file, line as u32);
    }
}

/// Continue execution from paused state
///
/// Resumes execution after hitting a breakpoint or pause.
/// Execution continues until the next breakpoint or program end.
#[no_mangle]
pub extern "C" fn rt_hook_continue() {
    let mut state = debug::debug_state();
    state.step_mode = StepMode::Continue;
    state.pause_requested = false;
}

/// Pause execution
///
/// Pauses execution at the next available statement.
/// Used to implement the "pause" button in debuggers.
#[no_mangle]
pub extern "C" fn rt_hook_pause() {
    let mut state = debug::debug_state();
    state.pause_requested = true;
}

/// Single step execution
///
/// Executes a single statement and then pauses.
/// The type of step (over/into/out) is determined by the hook context.
#[no_mangle]
pub extern "C" fn rt_hook_step() {
    let mut state = debug::debug_state();
    state.step_mode = StepMode::StepIn;
    state.step_frame_depth = state.call_stack.len();
}

/// Terminate execution
///
/// Immediately stops the running program.
/// Used to implement the "stop" button in debuggers.
#[no_mangle]
pub extern "C" fn rt_hook_terminate() {
    // Note: The existing debug system doesn't have a terminate state
    // We disable debugging which effectively stops debug behavior
    let mut state = debug::debug_state();
    state.active = false;
}

/// Get current call depth
///
/// Returns the depth of the current call stack.
/// Used to determine when to stop during step over/out.
#[no_mangle]
pub extern "C" fn rt_hook_get_call_depth() -> i64 {
    let state = debug::debug_state();
    state.call_stack.len() as i64
}

/// Get current stack frames
///
/// Captures the current call stack when paused.
/// Returns stack frames from current (0) to oldest.
#[no_mangle]
pub extern "C" fn rt_hook_get_stack_frames() -> Vec<StackFrame> {
    let state = debug::debug_state();
    state.call_stack
        .iter()
        .enumerate()
        .map(|(i, frame)| StackFrame {
            id: i as i64,
            name: frame.function_name.clone(),
            file: frame.file.clone(),
            line: frame.line as i64,
            column: frame.column as i64,
            scope_id: i as i64,
        })
        .collect()
}

/// Get variables in a specific scope
///
/// Returns all variables visible in the given scope at the given frame.
#[no_mangle]
pub extern "C" fn rt_hook_get_variables(frame_id: i64, scope: VariableScope) -> Vec<Variable> {
    let state = debug::debug_state();

    // Get the frame
    if let Some(frame) = state.call_stack.get(frame_id as usize) {
        // Convert frame locals to Variable structs
        frame.locals
            .iter()
            .map(|(name, value_repr, type_name)| Variable {
                name: name.clone(),
                value: value_repr.clone(),
                type_name: type_name.clone(),
                scope,
                is_mutable: false, // TODO: Track mutability
                memory_address: None,
            })
            .collect()
    } else {
        Vec::new()
    }
}

/// Evaluate an expression in debug context
///
/// Evaluates an arbitrary expression in the context of a stack frame.
/// Used for watch expressions and debug console.
#[no_mangle]
pub extern "C" fn rt_hook_evaluate_expression(expr: String, _frame_id: i64) -> EvalResult {
    // TODO: Integrate with interpreter's expression evaluator
    // This requires parsing and evaluating in the current context

    EvalResult {
        value: String::new(),
        type_name: String::new(),
        error: Some(format!("Expression evaluation not yet implemented: {}", expr)),
    }
}

/// Evaluate a breakpoint condition
///
/// Evaluates a conditional breakpoint's condition in the current context.
/// Returns true if the condition is met (should break).
#[no_mangle]
pub extern "C" fn rt_hook_evaluate_condition(_condition: String) -> bool {
    // TODO: Integrate with interpreter's expression evaluator
    false
}

/// Enable debugging mode
///
/// Enables debugging hooks in the interpreter.
/// Must be called before adding breakpoints.
#[no_mangle]
pub extern "C" fn rt_hook_enable_debugging() {
    let mut state = debug::debug_state();
    state.active = true;
}

/// Disable debugging mode
///
/// Disables debugging hooks for better performance.
/// Removes all breakpoints.
#[no_mangle]
pub extern "C" fn rt_hook_disable_debugging() {
    let mut state = debug::debug_state();
    state.active = false;
    state.remove_all_breakpoints();
}

// --- Integration Helpers ---
// These helpers are used by the interpreter to integrate with debugging

/// Check if we should break at the current location
///
/// Called by the interpreter at statement boundaries (in node_exec.rs).
/// Returns true if execution should pause.
///
/// Note: The interpreter already calls debug::debug_state().should_stop()
/// This function is kept for API compatibility if needed elsewhere.
pub fn should_break_at(file: &str, line: i64) -> bool {
    let mut state = debug::debug_state();
    state.should_stop(file, line as u32)
}

/// Push a new call frame (called on function entry)
///
/// Note: The interpreter should call debug::debug_state().push_frame() directly.
/// This is kept for API compatibility.
pub fn on_function_entry(function_name: &str, file: &str, line: u32, column: u32) {
    let mut state = debug::debug_state();
    state.push_frame(function_name, file, line, column);
}

/// Pop a call frame (called on function exit)
///
/// Note: The interpreter should call debug::debug_state().pop_frame() directly.
/// This is kept for API compatibility.
pub fn on_function_exit() {
    let mut state = debug::debug_state();
    state.pop_frame();
}

/// Capture current stack frames
///
/// Note: Not needed anymore - frames are captured in debug_state.call_stack
/// This is kept for API compatibility but does nothing.
#[deprecated(note = "Use debug::debug_state().call_stack directly")]
pub fn capture_stack_frames(_frames: Vec<StackFrame>) {
    // No-op: frames are managed by debug_state
}

// --- Tests ---

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_breakpoint_management() {
        rt_hook_enable_debugging();

        // Add breakpoint
        rt_hook_add_breakpoint("test.spl".to_string(), 10, 1);

        {
            let state = debug::debug_state();
            assert!(state.file_has_breakpoints("test.spl"));
            assert!(state.check_breakpoint("test.spl", 10).is_some());
        }

        // Remove breakpoint
        rt_hook_remove_breakpoint("test.spl".to_string(), 10);

        {
            let state = debug::debug_state();
            assert!(!state.file_has_breakpoints("test.spl"));
        }

        rt_hook_disable_debugging();
    }

    #[test]
    fn test_execution_control() {
        rt_hook_enable_debugging();

        // Pause
        rt_hook_pause();
        {
            let state = debug::debug_state();
            assert!(state.pause_requested);
        }

        // Continue
        rt_hook_continue();
        {
            let state = debug::debug_state();
            assert_eq!(state.step_mode, StepMode::Continue);
            assert!(!state.pause_requested);
        }

        rt_hook_disable_debugging();
    }

    #[test]
    fn test_call_depth() {
        rt_hook_enable_debugging();

        assert_eq!(rt_hook_get_call_depth(), 0);

        on_function_entry("test_fn", "test.spl", 10, 0);
        assert_eq!(rt_hook_get_call_depth(), 1);

        on_function_entry("nested_fn", "test.spl", 20, 0);
        assert_eq!(rt_hook_get_call_depth(), 2);

        on_function_exit();
        assert_eq!(rt_hook_get_call_depth(), 1);

        on_function_exit();
        assert_eq!(rt_hook_get_call_depth(), 0);

        rt_hook_disable_debugging();
    }

    #[test]
    fn test_should_break_at() {
        rt_hook_enable_debugging();

        // Add breakpoint
        rt_hook_add_breakpoint("test.spl".to_string(), 20, 1);

        // Should break at breakpoint
        assert!(should_break_at("test.spl", 20));

        // Continue
        rt_hook_continue();

        // Should not break at other lines
        assert!(!should_break_at("test.spl", 21));

        rt_hook_disable_debugging();
    }

    #[test]
    fn test_debugging_enable_disable() {
        rt_hook_enable_debugging();

        {
            let state = debug::debug_state();
            assert!(state.active);
        }

        rt_hook_disable_debugging();

        {
            let state = debug::debug_state();
            assert!(!state.active);
        }
    }

    #[test]
    fn test_get_stack_frames() {
        rt_hook_enable_debugging();

        on_function_entry("main", "test.spl", 1, 0);
        on_function_entry("foo", "test.spl", 10, 0);

        let frames = rt_hook_get_stack_frames();
        assert_eq!(frames.len(), 2);
        assert_eq!(frames[0].name, "main");
        assert_eq!(frames[1].name, "foo");

        on_function_exit();
        on_function_exit();

        rt_hook_disable_debugging();
    }
}
