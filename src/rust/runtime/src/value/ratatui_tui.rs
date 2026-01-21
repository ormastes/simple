//! Ratatui TUI FFI bridge for Simple TUI framework
//!
//! Provides FFI functions to expose Ratatui functionality to Simple language.
//! Ratatui is a modern, thread-safe (Send + Sync) terminal UI framework.
//!
//! # Ratatui Features
//!
//! - ✅ Thread-safe (Send + Sync) - works with FFI + static storage
//! - ✅ Rich widget library (Block, Paragraph, List, Table, etc.)
//! - ✅ Crossterm backend compatible
//! - ✅ Immediate-mode rendering
//! - ✅ Constraint-based layouts
//!
//! # API Reference
//!
//! - Main: https://ratatui.rs/
//! - Docs: https://docs.rs/ratatui
//! - Text Input: https://github.com/rhysd/tui-textarea

#![allow(dead_code)]

#[cfg(feature = "ratatui-tui")]
use crossterm::{
    event::{self, Event as CrosstermEvent, KeyCode, KeyModifiers},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};

#[cfg(feature = "ratatui-tui")]
use ratatui::{
    backend::CrosstermBackend,
    style::{Color, Style},
    widgets::{Block, Borders, Paragraph},
    Terminal,
};

use std::collections::HashMap;
use std::io::{self, Stdout};
use std::sync::{Arc, Mutex};

/// Handle counter for tracking Ratatui objects
static HANDLE_COUNTER: Mutex<u64> = Mutex::new(1);

/// Handle registry for Ratatui objects (Send + Sync compatible!)
static HANDLE_REGISTRY: Mutex<Option<HashMap<u64, RatatuiObject>>> = Mutex::new(None);

/// Ratatui object types (all are Send + Sync)
#[cfg(feature = "ratatui-tui")]
#[derive(Clone)]
enum RatatuiObject {
    Terminal(Arc<Mutex<Terminal<CrosstermBackend<Stdout>>>>),
    TextBuffer(Arc<Mutex<TextBuffer>>),
}

/// Simple text buffer for managing text input
#[cfg(feature = "ratatui-tui")]
#[derive(Clone)]
struct TextBuffer {
    lines: Vec<String>,
    cursor_line: usize,
    cursor_col: usize,
}

#[cfg(feature = "ratatui-tui")]
impl TextBuffer {
    fn new() -> Self {
        TextBuffer {
            lines: vec![String::new()],
            cursor_line: 0,
            cursor_col: 0,
        }
    }

    fn insert_char(&mut self, ch: char) {
        if self.cursor_line < self.lines.len() {
            self.lines[self.cursor_line].insert(self.cursor_col, ch);
            self.cursor_col += 1;
        }
    }

    fn backspace(&mut self) {
        if self.cursor_col > 0 {
            self.lines[self.cursor_line].remove(self.cursor_col - 1);
            self.cursor_col -= 1;
        } else if self.cursor_line > 0 {
            // Join with previous line
            let current_line = self.lines.remove(self.cursor_line);
            self.cursor_line -= 1;
            self.cursor_col = self.lines[self.cursor_line].len();
            self.lines[self.cursor_line].push_str(&current_line);
        }
    }

    fn insert_newline(&mut self) {
        let remaining = self.lines[self.cursor_line].split_off(self.cursor_col);
        self.cursor_line += 1;
        self.lines.insert(self.cursor_line, remaining);
        self.cursor_col = 0;
    }

    fn get_text(&self) -> String {
        self.lines.join("\n")
    }

    fn set_text(&mut self, text: &str) {
        self.lines = text.lines().map(|s| s.to_string()).collect();
        if self.lines.is_empty() {
            self.lines.push(String::new());
        }
        self.cursor_line = 0;
        self.cursor_col = 0;
    }
}

/// Initialize the handle registry
fn init_registry() {
    let mut registry = HANDLE_REGISTRY.lock().unwrap();
    if registry.is_none() {
        *registry = Some(HashMap::new());
    }
}

/// Allocate a new handle
fn alloc_handle() -> u64 {
    let mut counter = HANDLE_COUNTER.lock().unwrap();
    let handle = *counter;
    *counter += 1;
    handle
}

/// Store an object in the registry
#[cfg(feature = "ratatui-tui")]
fn store_object(obj: RatatuiObject) -> u64 {
    init_registry();
    let handle = alloc_handle();
    let mut registry = HANDLE_REGISTRY.lock().unwrap();
    if let Some(ref mut map) = *registry {
        map.insert(handle, obj);
    }
    handle
}

/// Retrieve an object from the registry
#[cfg(feature = "ratatui-tui")]
fn get_object(handle: u64) -> Option<RatatuiObject> {
    let registry = HANDLE_REGISTRY.lock().unwrap();
    if let Some(ref map) = *registry {
        map.get(&handle).cloned()
    } else {
        None
    }
}

/// Event structure passed to Simple
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct TuiEvent {
    pub event_type: u32, // 0=Key, 1=Mouse, 2=Resize
    pub key_code: u32,   // ASCII or special key code
    pub key_mods: u32,   // Shift=1, Ctrl=2, Alt=4
    pub char_value: u32, // Unicode character value (if printable)
}

// ============================================================================
// Terminal Management
// ============================================================================

/// Create and initialize terminal
///
/// # Returns
/// Handle to the terminal (u64), or 0 on error
#[no_mangle]
#[cfg(feature = "ratatui-tui")]
pub extern "C" fn ratatui_terminal_new() -> u64 {
    match enable_raw_mode() {
        Ok(_) => {}
        Err(e) => {
            eprintln!("Failed to enable raw mode: {:?}", e);
            return 0;
        }
    }

    let mut stdout = io::stdout();
    if let Err(e) = execute!(stdout, EnterAlternateScreen) {
        eprintln!("Failed to enter alternate screen: {:?}", e);
        let _ = disable_raw_mode();
        return 0;
    }

    let backend = CrosstermBackend::new(stdout);
    match Terminal::new(backend) {
        Ok(terminal) => {
            let term_obj = RatatuiObject::Terminal(Arc::new(Mutex::new(terminal)));
            store_object(term_obj)
        }
        Err(e) => {
            eprintln!("Failed to create terminal: {:?}", e);
            let _ = execute!(io::stdout(), LeaveAlternateScreen);
            let _ = disable_raw_mode();
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "ratatui-tui"))]
pub extern "C" fn ratatui_terminal_new() -> u64 {
    eprintln!("Ratatui feature not enabled. Build with --features ratatui-tui");
    0
}

/// Cleanup and destroy terminal
///
/// # Arguments
/// * `terminal_handle` - Handle to the terminal
#[no_mangle]
#[cfg(feature = "ratatui-tui")]
pub extern "C" fn ratatui_terminal_cleanup(terminal_handle: u64) {
    if let Some(RatatuiObject::Terminal(_term)) = get_object(terminal_handle) {
        // Terminal will be dropped, triggering cleanup
        let _ = execute!(io::stdout(), LeaveAlternateScreen);
        let _ = disable_raw_mode();

        // Remove from registry
        let mut registry = HANDLE_REGISTRY.lock().unwrap();
        if let Some(ref mut map) = *registry {
            map.remove(&terminal_handle);
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "ratatui-tui"))]
pub extern "C" fn ratatui_terminal_cleanup(_terminal_handle: u64) {
    // No-op
}

/// Clear the terminal screen
///
/// # Arguments
/// * `terminal_handle` - Handle to the terminal
#[no_mangle]
#[cfg(feature = "ratatui-tui")]
pub extern "C" fn ratatui_terminal_clear(terminal_handle: u64) {
    if let Some(RatatuiObject::Terminal(term)) = get_object(terminal_handle) {
        let mut term = term.lock().unwrap();
        let _ = term.clear();
    }
}

#[no_mangle]
#[cfg(not(feature = "ratatui-tui"))]
pub extern "C" fn ratatui_terminal_clear(_terminal_handle: u64) {
    // No-op
}

// ============================================================================
// Text Buffer Management
// ============================================================================

/// Create a new text buffer
///
/// # Returns
/// Handle to the text buffer (u64), or 0 on error
#[no_mangle]
#[cfg(feature = "ratatui-tui")]
pub extern "C" fn ratatui_textbuffer_new() -> u64 {
    let buffer = TextBuffer::new();
    let buffer_obj = RatatuiObject::TextBuffer(Arc::new(Mutex::new(buffer)));
    store_object(buffer_obj)
}

#[no_mangle]
#[cfg(not(feature = "ratatui-tui"))]
pub extern "C" fn ratatui_textbuffer_new() -> u64 {
    0
}

/// Insert a character into the text buffer
///
/// # Arguments
/// * `buffer_handle` - Handle to the text buffer
/// * `ch` - Character to insert (Unicode code point)
#[no_mangle]
#[cfg(feature = "ratatui-tui")]
pub extern "C" fn ratatui_textbuffer_insert_char(buffer_handle: u64, ch: u32) {
    if let Some(c) = char::from_u32(ch) {
        if let Some(RatatuiObject::TextBuffer(buffer)) = get_object(buffer_handle) {
            let mut buffer = buffer.lock().unwrap();
            buffer.insert_char(c);
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "ratatui-tui"))]
pub extern "C" fn ratatui_textbuffer_insert_char(_buffer_handle: u64, _ch: u32) {
    // No-op
}

/// Backspace in the text buffer
///
/// # Arguments
/// * `buffer_handle` - Handle to the text buffer
#[no_mangle]
#[cfg(feature = "ratatui-tui")]
pub extern "C" fn ratatui_textbuffer_backspace(buffer_handle: u64) {
    if let Some(RatatuiObject::TextBuffer(buffer)) = get_object(buffer_handle) {
        let mut buffer = buffer.lock().unwrap();
        buffer.backspace();
    }
}

#[no_mangle]
#[cfg(not(feature = "ratatui-tui"))]
pub extern "C" fn ratatui_textbuffer_backspace(_buffer_handle: u64) {
    // No-op
}

/// Insert newline in the text buffer
///
/// # Arguments
/// * `buffer_handle` - Handle to the text buffer
#[no_mangle]
#[cfg(feature = "ratatui-tui")]
pub extern "C" fn ratatui_textbuffer_newline(buffer_handle: u64) {
    if let Some(RatatuiObject::TextBuffer(buffer)) = get_object(buffer_handle) {
        let mut buffer = buffer.lock().unwrap();
        buffer.insert_newline();
    }
}

#[no_mangle]
#[cfg(not(feature = "ratatui-tui"))]
pub extern "C" fn ratatui_textbuffer_newline(_buffer_handle: u64) {
    // No-op
}

/// Get text from buffer
///
/// # Arguments
/// * `buffer_handle` - Handle to the text buffer
/// * `output` - Buffer to write text to
/// * `output_len` - Length of output buffer
///
/// # Returns
/// Actual length of text (may be longer than output_len if truncated)
#[no_mangle]
#[cfg(feature = "ratatui-tui")]
pub extern "C" fn ratatui_textbuffer_get_text(buffer_handle: u64, output: *mut u8, output_len: usize) -> usize {
    if output.is_null() {
        return 0;
    }

    if let Some(RatatuiObject::TextBuffer(buffer)) = get_object(buffer_handle) {
        let buffer = buffer.lock().unwrap();
        let text = buffer.get_text();
        let text_bytes = text.as_bytes();
        let copy_len = text_bytes.len().min(output_len);

        unsafe {
            std::ptr::copy_nonoverlapping(text_bytes.as_ptr(), output, copy_len);
        }

        text_bytes.len()
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "ratatui-tui"))]
pub extern "C" fn ratatui_textbuffer_get_text(_buffer_handle: u64, _output: *mut u8, _output_len: usize) -> usize {
    0
}

/// Set text in buffer
///
/// # Arguments
/// * `buffer_handle` - Handle to the text buffer
/// * `text` - Text to set (UTF-8 bytes)
/// * `text_len` - Length of text
#[no_mangle]
#[cfg(feature = "ratatui-tui")]
pub extern "C" fn ratatui_textbuffer_set_text(buffer_handle: u64, text: *const u8, text_len: usize) {
    if text.is_null() {
        return;
    }

    let text_bytes = unsafe { std::slice::from_raw_parts(text, text_len) };
    let text_str = match std::str::from_utf8(text_bytes) {
        Ok(s) => s,
        Err(_) => return,
    };

    if let Some(RatatuiObject::TextBuffer(buffer)) = get_object(buffer_handle) {
        let mut buffer = buffer.lock().unwrap();
        buffer.set_text(text_str);
    }
}

#[no_mangle]
#[cfg(not(feature = "ratatui-tui"))]
pub extern "C" fn ratatui_textbuffer_set_text(_buffer_handle: u64, _text: *const u8, _text_len: usize) {
    // No-op
}

// ============================================================================
// Rendering
// ============================================================================

/// Render text buffer to terminal
///
/// # Arguments
/// * `terminal_handle` - Handle to the terminal
/// * `buffer_handle` - Handle to the text buffer
/// * `prompt` - Prompt text (UTF-8 bytes)
/// * `prompt_len` - Length of prompt
#[no_mangle]
#[cfg(feature = "ratatui-tui")]
pub extern "C" fn ratatui_render_textbuffer(
    terminal_handle: u64,
    buffer_handle: u64,
    prompt: *const u8,
    prompt_len: usize,
) {
    if prompt.is_null() {
        return;
    }

    let prompt_bytes = unsafe { std::slice::from_raw_parts(prompt, prompt_len) };
    let prompt_str = match std::str::from_utf8(prompt_bytes) {
        Ok(s) => s,
        Err(_) => return,
    };

    if let (Some(RatatuiObject::Terminal(term)), Some(RatatuiObject::TextBuffer(buffer))) =
        (get_object(terminal_handle), get_object(buffer_handle))
    {
        let mut term = term.lock().unwrap();
        let buffer = buffer.lock().unwrap();

        let _ = term.draw(|f| {
            let size = f.area();

            // Create a paragraph with prompt and text
            let text = format!("{}{}", prompt_str, buffer.lines.join("\n"));
            let paragraph = Paragraph::new(text)
                .style(Style::default().fg(Color::White))
                .block(Block::default().borders(Borders::NONE));

            f.render_widget(paragraph, size);

            // Set cursor position
            let cursor_x = if buffer.cursor_line == 0 {
                (prompt_str.len() + buffer.cursor_col) as u16
            } else {
                buffer.cursor_col as u16
            };
            let cursor_y = buffer.cursor_line as u16;

            if cursor_x < size.width && cursor_y < size.height {
                f.set_cursor_position((cursor_x, cursor_y));
            }
        });
    }
}

#[no_mangle]
#[cfg(not(feature = "ratatui-tui"))]
pub extern "C" fn ratatui_render_textbuffer(
    _terminal_handle: u64,
    _buffer_handle: u64,
    _prompt: *const u8,
    _prompt_len: usize,
) {
    // No-op
}

// ============================================================================
// Event Handling
// ============================================================================

/// Read next event (blocking)
///
/// # Arguments
/// * `event_out` - Pointer to TuiEvent structure to fill
///
/// # Returns
/// 1 if event was read, 0 if no event or error
#[no_mangle]
#[cfg(feature = "ratatui-tui")]
pub extern "C" fn ratatui_read_event(event_out: *mut TuiEvent) -> i32 {
    if event_out.is_null() {
        return 0;
    }

    match event::read() {
        Ok(CrosstermEvent::Key(key)) => {
            let key_code = match key.code {
                KeyCode::Char(c) => c as u32,
                KeyCode::Enter => 13,
                KeyCode::Backspace => 8,
                KeyCode::Tab => 9,
                KeyCode::Esc => 27,
                KeyCode::Up => 0x1001,
                KeyCode::Down => 0x1002,
                KeyCode::Left => 0x1003,
                KeyCode::Right => 0x1004,
                _ => 0,
            };

            let char_value = match key.code {
                KeyCode::Char(c) => c as u32,
                _ => 0,
            };

            let mut key_mods = 0u32;
            if key.modifiers.contains(KeyModifiers::SHIFT) {
                key_mods |= 1;
            }
            if key.modifiers.contains(KeyModifiers::CONTROL) {
                key_mods |= 2;
            }
            if key.modifiers.contains(KeyModifiers::ALT) {
                key_mods |= 4;
            }

            unsafe {
                *event_out = TuiEvent {
                    event_type: 0, // Key event
                    key_code,
                    key_mods,
                    char_value,
                };
            }

            1
        }
        Ok(CrosstermEvent::Resize(w, h)) => {
            unsafe {
                *event_out = TuiEvent {
                    event_type: 2, // Resize event
                    key_code: w as u32,
                    key_mods: h as u32,
                    char_value: 0,
                };
            }
            1
        }
        Ok(_) => 0, // Ignore other events
        Err(_) => 0,
    }
}

#[no_mangle]
#[cfg(not(feature = "ratatui-tui"))]
pub extern "C" fn ratatui_read_event(_event_out: *mut TuiEvent) -> i32 {
    0
}

/// Read event with timeout (helper for Simple bindings that expect return by value)
///
/// # Arguments
/// * `timeout_ms` - Timeout in milliseconds (ignored for now, always blocks)
///
/// # Returns
/// TuiEvent struct (event_type=0 if no event)
#[no_mangle]
#[cfg(feature = "ratatui-tui")]
pub extern "C" fn ratatui_read_event_timeout(_timeout_ms: u64) -> TuiEvent {
    let mut event = TuiEvent {
        event_type: 0,
        key_code: 0,
        key_mods: 0,
        char_value: 0,
    };
    ratatui_read_event(&mut event as *mut TuiEvent);
    event
}

#[no_mangle]
#[cfg(not(feature = "ratatui-tui"))]
pub extern "C" fn ratatui_read_event_timeout(_timeout_ms: u64) -> TuiEvent {
    TuiEvent {
        event_type: 0,
        key_code: 0,
        key_mods: 0,
        char_value: 0,
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Destroy an object and remove from registry
///
/// # Arguments
/// * `handle` - Handle to the object
#[no_mangle]
pub extern "C" fn ratatui_object_destroy(handle: u64) {
    let mut registry = HANDLE_REGISTRY.lock().unwrap();
    if let Some(ref mut map) = *registry {
        map.remove(&handle);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_handle_allocation() {
        let h1 = alloc_handle();
        let h2 = alloc_handle();
        assert_ne!(h1, h2);
        assert!(h2 > h1);
    }

    #[test]
    #[cfg(feature = "ratatui-tui")]
    fn test_textbuffer_creation() {
        let handle = ratatui_textbuffer_new();
        assert_ne!(handle, 0, "TextBuffer creation should return non-zero handle");
        ratatui_object_destroy(handle);
    }

    #[test]
    #[cfg(not(feature = "ratatui-tui"))]
    fn test_textbuffer_creation_stub() {
        let handle = ratatui_textbuffer_new();
        assert_eq!(handle, 0, "Stub should return 0 when feature disabled");
    }

    #[test]
    fn test_registry_init() {
        init_registry();
        let registry = HANDLE_REGISTRY.lock().unwrap();
        assert!(registry.is_some());
    }
}
