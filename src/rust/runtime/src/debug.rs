//! Debug state management for the Simple language debugger.
//!
//! Provides breakpoint management, step control, call stack tracking,
//! and variable inspection. Used by both the interpreter (via hooks in
//! `exec_node`) and by FFI functions exposed to Simple-side debug tooling.

use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

use crate::value::RuntimeValue;

// ---------------------------------------------------------------------------
// DebugState – global, thread-safe debug state
// ---------------------------------------------------------------------------

/// Represents a single breakpoint.
#[derive(Debug, Clone)]
pub struct Breakpoint {
    pub id: u64,
    pub file: String,
    pub line: u32,
    pub condition: Option<String>,
    pub enabled: bool,
    pub hit_count: u64,
}

/// Call-stack frame captured by the interpreter.
#[derive(Debug, Clone)]
pub struct DebugFrame {
    pub function_name: String,
    pub file: String,
    pub line: u32,
    pub column: u32,
    /// Snapshot of local variable names → string representations.
    pub locals: Vec<(String, String, String)>, // (name, value_repr, type_name)
}

/// Step mode requested by the debugger.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepMode {
    Continue,
    StepOver,
    StepIn,
    StepOut,
}

/// Central debug state shared between the interpreter and debug tooling.
pub struct DebugState {
    pub active: bool,
    next_bp_id: u64,
    breakpoints: HashMap<String, Breakpoint>,
    pub step_mode: StepMode,
    pub step_frame_depth: usize,
    pub pause_requested: bool,
    pub call_stack: Vec<DebugFrame>,
    files_with_breakpoints: HashSet<String>,
}

impl DebugState {
    pub fn new() -> Self {
        Self {
            active: false,
            next_bp_id: 1,
            breakpoints: HashMap::new(),
            step_mode: StepMode::Continue,
            step_frame_depth: 0,
            pause_requested: false,
            call_stack: Vec::new(),
            files_with_breakpoints: HashSet::new(),
        }
    }

    pub fn add_breakpoint(&mut self, file: &str, line: u32, condition: Option<String>) -> u64 {
        let id = self.next_bp_id;
        self.next_bp_id += 1;
        let key = format!("{}:{}", file, line);
        self.breakpoints.insert(
            key,
            Breakpoint {
                id,
                file: file.to_string(),
                line,
                condition,
                enabled: true,
                hit_count: 0,
            },
        );
        self.files_with_breakpoints.insert(file.to_string());
        id
    }

    pub fn remove_breakpoint(&mut self, file: &str, line: u32) -> bool {
        let key = format!("{}:{}", file, line);
        let removed = self.breakpoints.remove(&key).is_some();
        if removed {
            let still_has = self.breakpoints.values().any(|bp| bp.file == file);
            if !still_has {
                self.files_with_breakpoints.remove(file);
            }
        }
        removed
    }

    pub fn remove_all_breakpoints(&mut self) {
        self.breakpoints.clear();
        self.files_with_breakpoints.clear();
    }

    pub fn list_breakpoints(&self) -> Vec<&Breakpoint> {
        self.breakpoints.values().collect()
    }

    #[inline]
    pub fn file_has_breakpoints(&self, file: &str) -> bool {
        self.files_with_breakpoints.contains(file)
    }

    pub fn check_breakpoint(&mut self, file: &str, line: u32) -> Option<u64> {
        let key = format!("{}:{}", file, line);
        if let Some(bp) = self.breakpoints.get_mut(&key) {
            if bp.enabled {
                bp.hit_count += 1;
                return Some(bp.id);
            }
        }
        None
    }

    pub fn should_stop(&mut self, file: &str, line: u32) -> bool {
        if !self.active {
            return false;
        }
        if self.pause_requested {
            self.pause_requested = false;
            return true;
        }
        if self.check_breakpoint(file, line).is_some() {
            return true;
        }
        let depth = self.call_stack.len();
        match self.step_mode {
            StepMode::Continue => false,
            StepMode::StepIn => true,
            StepMode::StepOver => depth <= self.step_frame_depth,
            StepMode::StepOut => depth < self.step_frame_depth,
        }
    }

    pub fn push_frame(&mut self, function_name: &str, file: &str, line: u32, column: u32) {
        self.call_stack.push(DebugFrame {
            function_name: function_name.to_string(),
            file: file.to_string(),
            line,
            column,
            locals: Vec::new(),
        });
    }

    pub fn pop_frame(&mut self) -> Option<DebugFrame> {
        self.call_stack.pop()
    }

    pub fn update_top_frame_location(&mut self, line: u32, column: u32) {
        if let Some(frame) = self.call_stack.last_mut() {
            frame.line = line;
            frame.column = column;
        }
    }

    pub fn set_top_frame_locals(&mut self, locals: Vec<(String, String, String)>) {
        if let Some(frame) = self.call_stack.last_mut() {
            frame.locals = locals;
        }
    }

    pub fn stack_depth(&self) -> usize {
        self.call_stack.len()
    }
}

// ---------------------------------------------------------------------------
// Global singleton
// ---------------------------------------------------------------------------

lazy_static::lazy_static! {
    pub static ref DEBUG_STATE: Mutex<DebugState> = Mutex::new(DebugState::new());
}

pub fn debug_state() -> std::sync::MutexGuard<'static, DebugState> {
    DEBUG_STATE.lock().unwrap()
}

// ---------------------------------------------------------------------------
// Helper: create a RuntimeValue string from a Rust &str
// ---------------------------------------------------------------------------

fn rv_string(s: &str) -> RuntimeValue {
    crate::value::rt_string_new(s.as_ptr(), s.len() as u64)
}

fn rv_array(items: Vec<RuntimeValue>) -> RuntimeValue {
    let arr = crate::value::rt_array_new(items.len() as u64);
    for item in items {
        crate::value::rt_array_push(arr, item);
    }
    arr
}

// ---------------------------------------------------------------------------
// FFI functions
// ---------------------------------------------------------------------------

#[no_mangle]
pub extern "C" fn rt_debug_set_active(active: i64) {
    debug_state().active = active != 0;
}

#[no_mangle]
pub extern "C" fn rt_debug_is_active() -> i64 {
    if debug_state().active { 1 } else { 0 }
}

#[no_mangle]
pub extern "C" fn rt_debug_add_breakpoint(file_ptr: i64, file_len: i64, line: i64) -> i64 {
    let file = unsafe {
        let slice = std::slice::from_raw_parts(file_ptr as *const u8, file_len as usize);
        std::str::from_utf8_unchecked(slice)
    };
    debug_state().add_breakpoint(file, line as u32, None) as i64
}

#[no_mangle]
pub extern "C" fn rt_debug_remove_breakpoint(file_ptr: i64, file_len: i64, line: i64) -> i64 {
    let file = unsafe {
        let slice = std::slice::from_raw_parts(file_ptr as *const u8, file_len as usize);
        std::str::from_utf8_unchecked(slice)
    };
    if debug_state().remove_breakpoint(file, line as u32) { 1 } else { 0 }
}

#[no_mangle]
pub extern "C" fn rt_debug_remove_all_breakpoints() {
    debug_state().remove_all_breakpoints();
}

#[no_mangle]
pub extern "C" fn rt_debug_list_breakpoints() -> RuntimeValue {
    let state = debug_state();
    let items: Vec<RuntimeValue> = state
        .list_breakpoints()
        .iter()
        .map(|bp| rv_string(&format!("{}:{}", bp.file, bp.line)))
        .collect();
    rv_array(items)
}

#[no_mangle]
pub extern "C" fn rt_debug_set_step_mode(mode: i64) {
    let mut state = debug_state();
    state.step_mode = match mode {
        1 => StepMode::StepOver,
        2 => StepMode::StepIn,
        3 => StepMode::StepOut,
        _ => StepMode::Continue,
    };
    state.step_frame_depth = state.call_stack.len();
}

#[no_mangle]
pub extern "C" fn rt_debug_pause() {
    debug_state().pause_requested = true;
}

#[no_mangle]
pub extern "C" fn rt_debug_continue() {
    let mut state = debug_state();
    state.step_mode = StepMode::Continue;
    state.pause_requested = false;
}

#[no_mangle]
pub extern "C" fn rt_debug_stack_depth() -> i64 {
    debug_state().call_stack.len() as i64
}

#[no_mangle]
pub extern "C" fn rt_debug_stack_trace() -> RuntimeValue {
    let state = debug_state();
    let items: Vec<RuntimeValue> = state
        .call_stack
        .iter()
        .rev()
        .enumerate()
        .map(|(i, f)| rv_string(&format!("#{} {} at {}:{}", i, f.function_name, f.file, f.line)))
        .collect();
    rv_array(items)
}

#[no_mangle]
pub extern "C" fn rt_debug_locals() -> RuntimeValue {
    let state = debug_state();
    let items = if let Some(frame) = state.call_stack.last() {
        frame
            .locals
            .iter()
            .map(|(name, val, ty)| rv_string(&format!("{} = {} : {}", name, val, ty)))
            .collect()
    } else {
        Vec::new()
    };
    rv_array(items)
}

#[no_mangle]
pub extern "C" fn rt_debug_current_file() -> RuntimeValue {
    let state = debug_state();
    if let Some(frame) = state.call_stack.last() {
        rv_string(&frame.file)
    } else {
        rv_string("")
    }
}

#[no_mangle]
pub extern "C" fn rt_debug_current_line() -> i64 {
    let state = debug_state();
    state.call_stack.last().map_or(0, |f| f.line as i64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn breakpoint_add_remove() {
        let mut ds = DebugState::new();
        let id = ds.add_breakpoint("test.spl", 10, None);
        assert!(id > 0);
        assert!(ds.file_has_breakpoints("test.spl"));
        assert!(ds.check_breakpoint("test.spl", 10).is_some());
        assert!(ds.remove_breakpoint("test.spl", 10));
        assert!(!ds.file_has_breakpoints("test.spl"));
    }

    #[test]
    fn step_modes() {
        let mut ds = DebugState::new();
        ds.active = true;
        ds.push_frame("main", "test.spl", 1, 0);

        ds.step_mode = StepMode::StepIn;
        assert!(ds.should_stop("test.spl", 5));

        ds.step_mode = StepMode::StepOver;
        ds.step_frame_depth = 1;
        assert!(ds.should_stop("test.spl", 5));

        ds.push_frame("inner", "test.spl", 10, 0);
        assert!(!ds.should_stop("test.spl", 11));
    }
}
