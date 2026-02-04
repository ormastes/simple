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
// - Global breakpoint registry (thread-safe with Arc<Mutex<>>)
// - Execution state tracking (running/paused/stopped/completed)
// - Stack frame capture on pause
// - Integration with interpreter at statement boundaries
//
// Thread Safety:
// - Debugging is single-threaded (one debugger per process)
// - Use thread-local storage for debug state
// - Breakpoint registry is global with Arc<Mutex<>>

use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use lazy_static::lazy_static;

// --- Type Definitions ---

/// Breakpoint type enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(i64)]
pub enum BreakpointType {
    Line = 0,
    Conditional = 1,
    Function = 2,
    Exception = 3,
    LogPoint = 4,
}

/// Execution state
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(i64)]
pub enum ExecutionState {
    Running = 0,
    Paused = 1,
    Stopped = 2,
    Completed = 3,
}

/// Variable scope enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(i64)]
pub enum VariableScope {
    Local = 0,
    Global = 1,
    Closure = 2,
    Argument = 3,
}

/// Stack frame information
#[derive(Debug, Clone)]
pub struct StackFrame {
    pub id: i64,
    pub name: String,
    pub file: String,
    pub line: i64,
    pub column: i64,
    pub scope_id: i64,
}

/// Variable information
#[derive(Debug, Clone)]
pub struct Variable {
    pub name: String,
    pub value: String,
    pub type_name: String,
    pub scope: VariableScope,
    pub is_mutable: bool,
    pub memory_address: Option<i64>,
}

/// Expression evaluation result
#[derive(Debug, Clone)]
pub struct EvalResult {
    pub value: String,
    pub type_name: String,
    pub error: Option<String>,
}

/// Breakpoint information
#[derive(Debug, Clone)]
pub struct Breakpoint {
    pub id: i64,
    pub file: String,
    pub line: i64,
    pub enabled: bool,
    pub bp_type: BreakpointType,
    pub condition: Option<String>,
    pub hit_count: i64,
}

/// Debug state for the current execution
#[derive(Debug)]
pub struct DebugState {
    /// All registered breakpoints (file -> line -> breakpoint)
    pub breakpoints: HashMap<String, HashMap<i64, Breakpoint>>,

    /// Current execution state
    pub execution_state: ExecutionState,

    /// Current call depth (for step over/out)
    pub call_depth: i64,

    /// Target call depth for step operations
    pub target_depth: Option<i64>,

    /// Current stack frames (captured when paused)
    pub current_frames: Vec<StackFrame>,

    /// Whether debugging is enabled
    pub debugging_enabled: bool,
}

impl DebugState {
    pub fn new() -> Self {
        DebugState {
            breakpoints: HashMap::new(),
            execution_state: ExecutionState::Running,
            call_depth: 0,
            target_depth: None,
            current_frames: Vec::new(),
            debugging_enabled: false,
        }
    }

    /// Check if a breakpoint exists at the given location
    pub fn has_breakpoint(&self, file: &str, line: i64) -> bool {
        if let Some(file_breakpoints) = self.breakpoints.get(file) {
            if let Some(bp) = file_breakpoints.get(&line) {
                return bp.enabled;
            }
        }
        false
    }

    /// Get breakpoint at location
    pub fn get_breakpoint(&self, file: &str, line: i64) -> Option<&Breakpoint> {
        self.breakpoints.get(file)?.get(&line)
    }

    /// Get mutable breakpoint at location
    pub fn get_breakpoint_mut(&mut self, file: &str, line: i64) -> Option<&mut Breakpoint> {
        self.breakpoints.get_mut(file)?.get_mut(&line)
    }
}

// --- Global Debug State ---

lazy_static! {
    /// Global debug state (thread-safe)
    static ref DEBUG_STATE: Arc<Mutex<DebugState>> = Arc::new(Mutex::new(DebugState::new()));
}

// --- FFI Function Implementations ---

/// Add a breakpoint at a specific line
///
/// Registers a breakpoint in the interpreter. When execution reaches this line,
/// the interpreter will pause and notify the debugger.
#[no_mangle]
pub extern "C" fn rt_hook_add_breakpoint(file: String, line: i64, id: i64) {
    let mut state = DEBUG_STATE.lock().unwrap();

    let breakpoint = Breakpoint {
        id,
        file: file.clone(),
        line,
        enabled: true,
        bp_type: BreakpointType::Line,
        condition: None,
        hit_count: 0,
    };

    state.breakpoints
        .entry(file)
        .or_insert_with(HashMap::new)
        .insert(line, breakpoint);
}

/// Remove a breakpoint
///
/// Removes a previously registered breakpoint.
#[no_mangle]
pub extern "C" fn rt_hook_remove_breakpoint(file: String, line: i64) {
    let mut state = DEBUG_STATE.lock().unwrap();

    if let Some(file_breakpoints) = state.breakpoints.get_mut(&file) {
        file_breakpoints.remove(&line);
    }
}

/// Enable or disable a breakpoint
///
/// Allows temporarily disabling a breakpoint without removing it.
#[no_mangle]
pub extern "C" fn rt_hook_set_breakpoint_enabled(file: String, line: i64, enabled: bool) {
    let mut state = DEBUG_STATE.lock().unwrap();

    if let Some(bp) = state.get_breakpoint_mut(&file, line) {
        bp.enabled = enabled;
    }
}

/// Continue execution from paused state
///
/// Resumes execution after hitting a breakpoint or pause.
/// Execution continues until the next breakpoint or program end.
#[no_mangle]
pub extern "C" fn rt_hook_continue() {
    let mut state = DEBUG_STATE.lock().unwrap();
    state.execution_state = ExecutionState::Running;
    state.target_depth = None;
}

/// Pause execution
///
/// Pauses execution at the next available statement.
/// Used to implement the "pause" button in debuggers.
#[no_mangle]
pub extern "C" fn rt_hook_pause() {
    let mut state = DEBUG_STATE.lock().unwrap();
    state.execution_state = ExecutionState::Paused;
}

/// Single step execution
///
/// Executes a single statement and then pauses.
/// The type of step (over/into/out) is determined by the hook context.
#[no_mangle]
pub extern "C" fn rt_hook_step() {
    let mut state = DEBUG_STATE.lock().unwrap();
    state.execution_state = ExecutionState::Paused;
    // Step will be handled by interpreter checking target_depth
    // For step over: target_depth = Some(current_depth)
    // For step into: target_depth = None
    // For step out: target_depth = Some(current_depth - 1)
}

/// Terminate execution
///
/// Immediately stops the running program.
/// Used to implement the "stop" button in debuggers.
#[no_mangle]
pub extern "C" fn rt_hook_terminate() {
    let mut state = DEBUG_STATE.lock().unwrap();
    state.execution_state = ExecutionState::Stopped;
}

/// Get current call depth
///
/// Returns the depth of the current call stack.
/// Used to determine when to stop during step over/out.
#[no_mangle]
pub extern "C" fn rt_hook_get_call_depth() -> i64 {
    let state = DEBUG_STATE.lock().unwrap();
    state.call_depth
}

/// Get current stack frames
///
/// Captures the current call stack when paused.
/// Returns stack frames from current (0) to oldest.
#[no_mangle]
pub extern "C" fn rt_hook_get_stack_frames() -> Vec<StackFrame> {
    let state = DEBUG_STATE.lock().unwrap();
    state.current_frames.clone()
}

/// Get variables in a specific scope
///
/// Returns all variables visible in the given scope at the given frame.
#[no_mangle]
pub extern "C" fn rt_hook_get_variables(frame_id: i64, scope: VariableScope) -> Vec<Variable> {
    // TODO: Integrate with interpreter's variable tracking
    // This requires accessing the interpreter's execution context
    // For now, return empty list (placeholder)

    // Implementation notes:
    // 1. Get the stack frame at frame_id
    // 2. Access the interpreter's scope/environment at that frame
    // 3. Filter variables by scope type (Local/Global/Closure/Argument)
    // 4. Convert runtime values to Variable structs

    Vec::new()
}

/// Evaluate an expression in debug context
///
/// Evaluates an arbitrary expression in the context of a stack frame.
/// Used for watch expressions and debug console.
#[no_mangle]
pub extern "C" fn rt_hook_evaluate_expression(expr: String, frame_id: i64) -> EvalResult {
    // TODO: Integrate with interpreter's expression evaluator
    // This requires:
    // 1. Parse the expression string
    // 2. Get the execution context at frame_id
    // 3. Evaluate the expression in that context
    // 4. Return the result or error

    // For now, return placeholder error
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
pub extern "C" fn rt_hook_evaluate_condition(condition: String) -> bool {
    // TODO: Integrate with interpreter's expression evaluator
    // Similar to evaluate_expression but returns bool

    // For now, always return false (don't break)
    false
}

/// Enable debugging mode
///
/// Enables debugging hooks in the interpreter.
/// Must be called before adding breakpoints.
#[no_mangle]
pub extern "C" fn rt_hook_enable_debugging() {
    let mut state = DEBUG_STATE.lock().unwrap();
    state.debugging_enabled = true;
}

/// Disable debugging mode
///
/// Disables debugging hooks for better performance.
/// Removes all breakpoints.
#[no_mangle]
pub extern "C" fn rt_hook_disable_debugging() {
    let mut state = DEBUG_STATE.lock().unwrap();
    state.debugging_enabled = false;
    state.breakpoints.clear();
    state.execution_state = ExecutionState::Running;
}

// --- Integration Helpers ---

/// Check if we should break at the current location
///
/// Called by the interpreter at statement boundaries.
/// Returns true if execution should pause.
pub fn should_break_at(file: &str, line: i64) -> bool {
    let mut state = DEBUG_STATE.lock().unwrap();

    if !state.debugging_enabled {
        return false;
    }

    // Check execution state
    match state.execution_state {
        ExecutionState::Stopped | ExecutionState::Completed => {
            return false;
        }
        ExecutionState::Paused => {
            return true;
        }
        ExecutionState::Running => {
            // Check breakpoints
            if let Some(bp) = state.get_breakpoint_mut(file, line) {
                if bp.enabled {
                    bp.hit_count += 1;

                    // Check condition if it's a conditional breakpoint
                    if let Some(ref condition) = bp.condition {
                        if !rt_hook_evaluate_condition(condition.clone()) {
                            return false;
                        }
                    }

                    // Break here
                    state.execution_state = ExecutionState::Paused;
                    return true;
                }
            }
        }
    }

    false
}

/// Update call depth (called on function entry/exit)
pub fn on_function_entry() {
    let mut state = DEBUG_STATE.lock().unwrap();
    state.call_depth += 1;
}

pub fn on_function_exit() {
    let mut state = DEBUG_STATE.lock().unwrap();
    state.call_depth -= 1;

    // Check if we should pause (for step out)
    if let Some(target) = state.target_depth {
        if state.call_depth <= target {
            state.execution_state = ExecutionState::Paused;
            state.target_depth = None;
        }
    }
}

/// Capture current stack frames
///
/// Called when execution pauses to capture the call stack.
pub fn capture_stack_frames(frames: Vec<StackFrame>) {
    let mut state = DEBUG_STATE.lock().unwrap();
    state.current_frames = frames;
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

        let state = DEBUG_STATE.lock().unwrap();
        assert!(state.has_breakpoint("test.spl", 10));

        drop(state);

        // Disable breakpoint
        rt_hook_set_breakpoint_enabled("test.spl".to_string(), 10, false);

        let state = DEBUG_STATE.lock().unwrap();
        assert!(!state.has_breakpoint("test.spl", 10));

        drop(state);

        // Remove breakpoint
        rt_hook_remove_breakpoint("test.spl".to_string(), 10);

        let state = DEBUG_STATE.lock().unwrap();
        assert!(state.get_breakpoint("test.spl", 10).is_none());
    }

    #[test]
    fn test_execution_control() {
        rt_hook_enable_debugging();

        // Start paused
        rt_hook_pause();

        let state = DEBUG_STATE.lock().unwrap();
        assert_eq!(state.execution_state, ExecutionState::Paused);

        drop(state);

        // Continue
        rt_hook_continue();

        let state = DEBUG_STATE.lock().unwrap();
        assert_eq!(state.execution_state, ExecutionState::Running);

        drop(state);

        // Terminate
        rt_hook_terminate();

        let state = DEBUG_STATE.lock().unwrap();
        assert_eq!(state.execution_state, ExecutionState::Stopped);
    }

    #[test]
    fn test_call_depth() {
        rt_hook_enable_debugging();

        assert_eq!(rt_hook_get_call_depth(), 0);

        on_function_entry();
        assert_eq!(rt_hook_get_call_depth(), 1);

        on_function_entry();
        assert_eq!(rt_hook_get_call_depth(), 2);

        on_function_exit();
        assert_eq!(rt_hook_get_call_depth(), 1);

        on_function_exit();
        assert_eq!(rt_hook_get_call_depth(), 0);
    }

    #[test]
    fn test_should_break_at() {
        rt_hook_enable_debugging();

        // Add breakpoint
        rt_hook_add_breakpoint("test.spl".to_string(), 20, 1);

        // Should break at breakpoint
        assert!(should_break_at("test.spl", 20));

        // Should be paused now
        let state = DEBUG_STATE.lock().unwrap();
        assert_eq!(state.execution_state, ExecutionState::Paused);

        drop(state);

        // Continue
        rt_hook_continue();

        // Should not break at other lines
        assert!(!should_break_at("test.spl", 21));
    }

    #[test]
    fn test_debugging_enable_disable() {
        rt_hook_enable_debugging();

        let state = DEBUG_STATE.lock().unwrap();
        assert!(state.debugging_enabled);

        drop(state);

        rt_hook_disable_debugging();

        let state = DEBUG_STATE.lock().unwrap();
        assert!(!state.debugging_enabled);
        assert!(state.breakpoints.is_empty());
    }
}
