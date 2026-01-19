//! TUI (Text User Interface) extern functions
//!
//! Ratatui FFI bindings for building terminal UIs.

use crate::error::CompileError;
use crate::value::Value;

// TuiEvent struct matches the C ABI struct in ratatui_tui.rs
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct TuiEvent {
    pub event_type: u32,
    pub key_code: u32,
    pub key_mods: u32,
    pub char_value: u32,
}

// Extern declarations for Ratatui FFI functions
extern "C" {
    fn ratatui_terminal_new() -> u64;
    fn ratatui_terminal_cleanup(terminal: u64);
    fn ratatui_terminal_clear(terminal: u64);
    fn ratatui_textbuffer_new() -> u64;
    fn ratatui_textbuffer_insert_char(buffer: u64, code: u32);
    fn ratatui_textbuffer_backspace(buffer: u64);
    fn ratatui_textbuffer_newline(buffer: u64);
    fn ratatui_textbuffer_get_text(buf_ptr: *mut u8, buf_len: usize) -> usize;
    fn ratatui_textbuffer_set_text(text_ptr: *const u8, text_len: usize);
    fn ratatui_render_textbuffer(terminal: u64, buffer: u64, prompt_ptr: *const u8, prompt_len: usize);
    fn ratatui_read_event_timeout(timeout_ms: u64) -> TuiEvent;
    fn ratatui_object_destroy(handle: u64);
}

/// Create new Ratatui terminal
pub fn ratatui_terminal_new_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let handle = unsafe { ratatui_terminal_new() };
    Ok(Value::Int(handle as i64))
}

/// Cleanup Ratatui terminal
pub fn ratatui_terminal_cleanup_fn(args: &[Value]) -> Result<Value, CompileError> {
    let terminal = args
        .first()
        .ok_or_else(|| CompileError::Semantic("ratatui_terminal_cleanup expects 1 argument".into()))?
        .as_int()? as u64;
    unsafe {
        ratatui_terminal_cleanup(terminal);
    }
    Ok(Value::Nil)
}

/// Clear Ratatui terminal
pub fn ratatui_terminal_clear_fn(args: &[Value]) -> Result<Value, CompileError> {
    let terminal = args
        .first()
        .ok_or_else(|| CompileError::Semantic("ratatui_terminal_clear expects 1 argument".into()))?
        .as_int()? as u64;
    unsafe {
        ratatui_terminal_clear(terminal);
    }
    Ok(Value::Nil)
}

/// Create new text buffer
pub fn ratatui_textbuffer_new_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let handle = unsafe { ratatui_textbuffer_new() };
    Ok(Value::Int(handle as i64))
}

/// Insert character into text buffer
pub fn ratatui_textbuffer_insert_char_fn(args: &[Value]) -> Result<Value, CompileError> {
    let buffer = args
        .get(0)
        .ok_or_else(|| CompileError::Semantic("ratatui_textbuffer_insert_char expects 2 arguments".into()))?
        .as_int()? as u64;
    let code = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("ratatui_textbuffer_insert_char expects 2 arguments".into()))?
        .as_int()? as u32;
    unsafe {
        ratatui_textbuffer_insert_char(buffer, code);
    }
    Ok(Value::Nil)
}

/// Backspace in text buffer
pub fn ratatui_textbuffer_backspace_fn(args: &[Value]) -> Result<Value, CompileError> {
    let buffer = args
        .first()
        .ok_or_else(|| CompileError::Semantic("ratatui_textbuffer_backspace expects 1 argument".into()))?
        .as_int()? as u64;
    unsafe {
        ratatui_textbuffer_backspace(buffer);
    }
    Ok(Value::Nil)
}

/// Newline in text buffer
pub fn ratatui_textbuffer_newline_fn(args: &[Value]) -> Result<Value, CompileError> {
    let buffer = args
        .first()
        .ok_or_else(|| CompileError::Semantic("ratatui_textbuffer_newline expects 1 argument".into()))?
        .as_int()? as u64;
    unsafe {
        ratatui_textbuffer_newline(buffer);
    }
    Ok(Value::Nil)
}

/// Destroy Ratatui object (terminal or buffer)
pub fn ratatui_object_destroy_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("ratatui_object_destroy expects 1 argument".into()))?
        .as_int()? as u64;
    unsafe {
        ratatui_object_destroy(handle);
    }
    Ok(Value::Nil)
}
