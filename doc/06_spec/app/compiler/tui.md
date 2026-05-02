# Simple TUI Framework Specification

A terminal user interface framework for Simple language with Ratatui backend integration.

## Contents

1. [Architecture](#1-architecture)
2. [Backend Integration](#2-backend-integration)
3. [Widget System](#3-widget-system)
4. [Event Handling](#4-event-handling)
5. [REPL Integration](#5-repl-integration)
6. [Testing Strategy](#6-testing-strategy)

---

## 1. Architecture

### 1.1 Overview

The Simple TUI framework provides terminal-based user interfaces through a layered architecture:

```
┌──────────────────────────────────────────┐
│   Simple Applications                    │  ← REPL, tools written in Simple
│   (simple/app/repl/, simple/app/*)      │
├──────────────────────────────────────────┤
│   Simple TUI Library                     │  ← Widgets, rendering (Simple)
│   (simple/std_lib/src/ui/tui/)          │
├──────────────────────────────────────────┤
│   Ratatui FFI Bridge (Send + Sync ✅)    │  ← Rust ↔ Simple bridge
│   (src/runtime/src/value/ratatui_tui.rs)│
├──────────────────────────────────────────┤
│   Ratatui Framework                      │  ← Terminal abstraction (Rust)
│   (ratatui = "0.28")                     │
├──────────────────────────────────────────┤
│   Crossterm Backend                      │  ← Platform-specific
│   (Windows, Linux, macOS)                │
└──────────────────────────────────────────┘
```

### 1.2 Design Principles

1. **Simple-first**: Primary API surface in Simple language
2. **FFI-backed**: Performance-critical operations in Rust via Ratatui
3. **Thread-safe**: Ratatui implements `Send + Sync` for multi-threaded use
4. **Immediate-mode**: Redraw UI each frame (Ratatui pattern)
5. **Event-driven**: Keyboard/mouse event dispatch via Crossterm
6. **Cross-platform**: Works on Windows, Linux, macOS

### 1.3 Module Organization

```
simple/std_lib/src/ui/tui/
├── __init__.spl           # Public API exports
├── renderer.spl           # TuiRenderer (Ratatui backend)
├── widgets.spl            # Pre-built widgets
├── events.spl             # Event types and handling
├── layout.spl             # Layout algorithms
├── colors.spl             # Color definitions
└── backend/
    ├── __init__.spl       # Backend abstraction
    └── ratatui.spl        # Ratatui FFI bindings
```

---

## 2. Backend Integration

### 2.1 Ratatui Backend

**Purpose**: Provide thread-safe terminal UI framework for:
- Terminal management with alternate screen
- Text buffer editing (multi-line)
- Immediate-mode rendering
- Cross-platform event handling
- Thread-safe architecture (`Send + Sync`)

**Dependencies**:
- `ratatui = "0.28"` - Modern TUI framework
- `crossterm = "0.28"` - Cross-platform terminal backend

**Feature Flag**: `ratatui-tui` in `src/runtime/Cargo.toml`

### 2.2 FFI Bridge Functions

**Location**: `src/runtime/src/value/ratatui_tui.rs` (630 lines)

**Thread Safety**: All types implement `Send + Sync` ✅

#### 2.2.1 Terminal Management

```rust
// Create terminal with alternate screen
#[no_mangle]
pub extern "C" fn ratatui_terminal_new() -> u64 {
    // Enable raw mode, enter alternate screen
    // Create Terminal<CrosstermBackend<Stdout>>
    // Return handle (Arc<Mutex<Terminal>> stored in registry)
}

// Cleanup and restore terminal state
#[no_mangle]
pub extern "C" fn ratatui_terminal_cleanup(terminal_handle: u64) {
    // Leave alternate screen
    // Disable raw mode
    // Remove from handle registry
}

// Clear terminal screen
#[no_mangle]
pub extern "C" fn ratatui_terminal_clear(terminal_handle: u64) {
    // Clear screen content
}
```

#### 2.2.2 Text Buffer Operations

Ratatui uses a custom `TextBuffer` for multi-line text editing:

```rust
// Create empty text buffer
#[no_mangle]
pub extern "C" fn ratatui_textbuffer_new() -> u64 {
    // Create TextBuffer { lines: vec![], cursor_line: 0, cursor_col: 0 }
    // Return handle (Arc<Mutex<TextBuffer>>)
}

// Insert character at cursor position
#[no_mangle]
pub extern "C" fn ratatui_textbuffer_insert_char(
    buffer_handle: u64,
    ch: u32  // Unicode code point
) {
    // Insert char at current cursor position
    // Advance cursor column
}

// Delete character before cursor (backspace)
#[no_mangle]
pub extern "C" fn ratatui_textbuffer_backspace(buffer_handle: u64) {
    // If cursor_col > 0: delete char at cursor_col-1, move cursor back
    // If cursor_col == 0 and cursor_line > 0: join with previous line
}

// Insert newline (split current line)
#[no_mangle]
pub extern "C" fn ratatui_textbuffer_newline(buffer_handle: u64) {
    // Split current line at cursor position
    // Move to next line, cursor_col = 0
}

// Get full text content
#[no_mangle]
pub extern "C" fn ratatui_textbuffer_get_text(
    buffer_handle: u64,
    buffer: *mut u8,
    buffer_len: usize
) -> usize {
    // Join all lines with '\n'
    // Copy to buffer, return actual length
}

// Set full text content
#[no_mangle]
pub extern "C" fn ratatui_textbuffer_set_text(
    buffer_handle: u64,
    text: *const u8,
    text_len: usize
) {
    // Split text by '\n', replace all lines
    // Reset cursor to (0, 0)
}
```

#### 2.2.3 Rendering

Ratatui uses immediate-mode rendering - redraw UI each frame:

```rust
// Render text buffer to terminal with prompt
#[no_mangle]
pub extern "C" fn ratatui_render_textbuffer(
    terminal_handle: u64,
    buffer_handle: u64,
    prompt: *const u8,
    prompt_len: usize
) {
    // terminal.draw(|f| {
    //     let text = format!("{}{}", prompt, buffer.get_text());
    //     let paragraph = Paragraph::new(text)
    //         .style(Style::default().fg(Color::White));
    //     f.render_widget(paragraph, f.area());
    //
    //     // Set cursor position (prompt_len + cursor_col, cursor_line)
    //     f.set_cursor_position((x, y));
    // });
}
```

#### 2.2.4 Event Handling

Events are polled using Crossterm:

```rust
// Event structure passed to Simple
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct TuiEvent {
    pub event_type: u32,  // 0=Key, 1=Mouse, 2=Resize
    pub key_code: u32,    // ASCII or special key code
    pub key_mods: u32,    // Shift=1, Ctrl=2, Alt=4
    pub char_value: u32,  // Unicode character value (if printable)
}

// Read terminal event with timeout
#[no_mangle]
pub extern "C" fn ratatui_read_event(timeout_ms: u64) -> TuiEvent {
    // Poll for event with timeout
    // Convert crossterm::event::Event → TuiEvent
    // Return event (or event_type=0 if timeout)
}
```

**Key Code Mapping**:
- **Printable**: ASCII/Unicode value (e.g., 'a' = 97, '1' = 49)
- **Enter**: 13
- **Backspace**: 8
- **Tab**: 9
- **Escape**: 27
- **Arrows**: Up=0x2001, Down=0x2002, Left=0x2003, Right=0x2004
- **Function**: F1=0x1001, F2=0x1002, etc.

#### 2.2.5 Lifecycle

```rust
// Destroy any Ratatui object by handle
#[no_mangle]
pub extern "C" fn ratatui_object_destroy(handle: u64) {
    // Remove from handle registry
    // Arc<Mutex<>> will be dropped automatically
}
```

### 2.3 Simple Language Bindings

**Location**: `simple/std_lib/src/ui/tui/backend/ratatui.spl`

```simple
# Ratatui FFI bindings

use ffi

# Opaque handles
pub type TerminalHandle = u64
pub type TextBufferHandle = u64

# Terminal management
pub fn terminal_new() -> TerminalHandle:
    return ffi.call("ratatui_terminal_new")

pub fn terminal_cleanup(terminal: TerminalHandle):
    ffi.call("ratatui_terminal_cleanup", terminal)

pub fn terminal_clear(terminal: TerminalHandle):
    ffi.call("ratatui_terminal_clear", terminal)

# Text buffer operations
pub fn textbuffer_new() -> TextBufferHandle:
    return ffi.call("ratatui_textbuffer_new")

pub fn textbuffer_insert_char(buffer: TextBufferHandle, ch: char):
    ffi.call("ratatui_textbuffer_insert_char", buffer, ch.to_u32())

pub fn textbuffer_backspace(buffer: TextBufferHandle):
    ffi.call("ratatui_textbuffer_backspace", buffer)

pub fn textbuffer_newline(buffer: TextBufferHandle):
    ffi.call("ratatui_textbuffer_newline", buffer)

pub fn textbuffer_get_text(buffer: TextBufferHandle) -> String:
    let mut buf = [0u8; 8192]
    let len = ffi.call("ratatui_textbuffer_get_text", buffer, buf.as_mut_ptr(), buf.len())
    return String::from_utf8(&buf[0..len]).unwrap()

pub fn textbuffer_set_text(buffer: TextBufferHandle, text: &str):
    ffi.call("ratatui_textbuffer_set_text", buffer, text.as_ptr(), text.len())

# Rendering
pub fn render_textbuffer(terminal: TerminalHandle, buffer: TextBufferHandle, prompt: &str):
    ffi.call("ratatui_render_textbuffer", terminal, buffer, prompt.as_ptr(), prompt.len())

# Event handling
pub enum EventType:
    Key = 0
    Mouse = 1
    Resize = 2

pub struct TuiEvent:
    pub event_type: u32
    pub key_code: u32
    pub key_mods: u32
    pub char_value: u32

pub fn read_event(timeout_ms: u64) -> TuiEvent:
    return ffi.call("ratatui_read_event", timeout_ms)

# Key code constants
pub const KEY_ENTER: u32 = 13
pub const KEY_BACKSPACE: u32 = 8
pub const KEY_TAB: u32 = 9
pub const KEY_ESCAPE: u32 = 27
pub const KEY_DELETE: u32 = 127

# Arrow keys
pub const KEY_UP: u32 = 0x2001
pub const KEY_DOWN: u32 = 0x2002
pub const KEY_LEFT: u32 = 0x2003
pub const KEY_RIGHT: u32 = 0x2004

# Function keys
pub const KEY_F1: u32 = 0x1001
pub const KEY_F2: u32 = 0x1002
# ... etc

# Modifiers (bit flags)
pub const MOD_SHIFT: u32 = 1
pub const MOD_CTRL: u32 = 2
pub const MOD_ALT: u32 = 4

# Lifecycle
pub fn object_destroy(handle: u64):
    ffi.call("ratatui_object_destroy", handle)
```

---

## 3. Widget System

### 3.1 Existing Widgets

Existing widgets in `simple/std_lib/src/ui/tui/widgets.spl` will be updated to use Ratatui backend:

- **Menu**: Vertical selectable list
- **Dialog**: Modal dialog boxes
- **ProgressBar**: Progress indicator
- **TextInput**: Single-line text input (using TextBuffer)
- **ScrollList**: Scrollable item list

### 3.2 New Ratatui-backed Widgets

#### 3.2.1 TextBuffer Widget

```simple
# simple/std_lib/src/ui/tui/widgets/textbuffer.spl

use ui.tui.backend.ratatui.*

pub struct TextBufferWidget:
    buffer: TextBufferHandle
    terminal: TerminalHandle

impl TextBufferWidget:
    pub fn new(terminal: TerminalHandle) -> TextBufferWidget:
        let buffer = textbuffer_new()
        return TextBufferWidget { buffer: buffer, terminal: terminal }

    pub fn insert_char(self, ch: char):
        textbuffer_insert_char(self.buffer, ch)

    pub fn backspace(self):
        textbuffer_backspace(self.buffer)

    pub fn newline(self):
        textbuffer_newline(self.buffer)

    pub fn get_text(self) -> String:
        return textbuffer_get_text(self.buffer)

    pub fn set_text(self, text: &str):
        textbuffer_set_text(self.buffer, text)

    pub fn render(self, prompt: &str):
        render_textbuffer(self.terminal, self.buffer, prompt)
```

#### 3.2.2 LineEditor (REPL Widget)

```simple
# simple/std_lib/src/ui/tui/widgets/line_editor.spl

use ui.tui.backend.ratatui.*

pub struct LineEditor:
    buffer: TextBufferWidget
    lines: Array[String]
    in_multiline: bool
    on_submit: Option[fn(String)]

impl LineEditor:
    pub fn new(terminal: TerminalHandle) -> LineEditor:
        let buffer = TextBufferWidget::new(terminal)
        return LineEditor {
            buffer: buffer,
            lines: [],
            in_multiline: false,
            on_submit: None
        }

    pub fn on_submit(self, callback: fn(String)):
        self.on_submit = Some(callback)

    pub fn handle_key(self, key: u32, mods: u32):
        # Handle Enter, Backspace, etc.
        match key:
            case 13:  # Enter
                self.handle_enter()
            case 8:   # Backspace
                self.handle_backspace()
            case _:
                # Regular character input handled by textbox
                pass

    fn handle_enter(self):
        let line = self.buffer.get_text()
        if line.trim_end().ends_with(':'):
            # Enter multiline mode
            self.lines.push(line)
            self.in_multiline = true
            # Auto-indent
            let indent = self.calculate_indent(&line) + 4
            self.buffer.set_text(&(" ".repeat(indent)))
        else if self.in_multiline:
            if line.trim().is_empty():
                # Complete multiline block
                let full_input = self.lines.join("\n")
                self.lines.clear()
                self.in_multiline = false
                if let Some(callback) = self.on_submit:
                    callback(full_input)
                self.buffer.set_text("")
            else:
                # Continue multiline
                self.lines.push(line)
                let indent = self.calculate_indent(&line)
                self.buffer.set_text(&(" ".repeat(indent)))
        else:
            # Single line complete
            if let Some(callback) = self.on_submit:
                callback(line)
            self.buffer.set_text("")

    fn handle_backspace(self):
        let text = self.buffer.get_text()

        # Smart backspace: delete 4 spaces in leading whitespace
        let leading_spaces = text.chars().take_while(|c| c == ' ').count()
        let cursor_pos = text.len()  # Cursor at end

        if cursor_pos == leading_spaces and cursor_pos >= 4:
            # Delete 4 spaces
            let new_text = &text[0..cursor_pos-4]
            self.buffer.set_text(new_text)
        else:
            # Normal backspace (handled by buffer)
            self.buffer.backspace()

    fn calculate_indent(self, line: &str) -> usize:
        return line.chars().take_while(|c| c == ' ').count()
```

---

## 4. Event Handling

### 4.1 Event Loop

Ratatui uses manual event polling. Simple code polls and handles events:

```simple
use ui.tui.backend.ratatui.*

fn main():
    let terminal = terminal_new()
    let editor = LineEditor::new(terminal)

    editor.on_submit(fn(input: String):
        # Execute input
        execute_repl_input(input)
    )

    # Event loop
    let mut running = true
    while running:
        # Render current state
        editor.render(">>> ")

        # Poll for events (100ms timeout)
        let event = read_event(100)

        # Handle event
        if event.event_type == EventType::Key:
            if event.key_code == KEY_ESCAPE:
                running = false
            else:
                editor.handle_key(event.key_code, event.key_mods, event.char_value)

    terminal_cleanup(terminal)
```

### 4.2 Key Codes

Standard ASCII + special keys (from Ratatui/Crossterm):

```simple
pub const KEY_ENTER: u32 = 13
pub const KEY_BACKSPACE: u32 = 8
pub const KEY_TAB: u32 = 9
pub const KEY_ESCAPE: u32 = 27
pub const KEY_DELETE: u32 = 127

# Function keys
pub const KEY_F1: u32 = 0x1001
pub const KEY_F2: u32 = 0x1002
# ... etc

# Arrow keys
pub const KEY_UP: u32 = 0x2001
pub const KEY_DOWN: u32 = 0x2002
pub const KEY_LEFT: u32 = 0x2003
pub const KEY_RIGHT: u32 = 0x2004

# Modifiers (bit flags)
pub const MOD_SHIFT: u32 = 1
pub const MOD_CTRL: u32 = 2
pub const MOD_ALT: u32 = 4
```

---

## 5. REPL Integration

### 5.1 REPL Application Structure

```
simple/app/repl/
├── main.spl              # REPL entry point
├── editor.spl            # LineEditor logic
├── executor.spl          # Code execution
└── history.spl           # Command history
```

### 5.2 REPL Main

**File**: `simple/app/repl/main.spl`

```simple
use ui.tui.backend.ratatui.*
use ui.tui.widgets.line_editor.*
use compiler.runner.*

pub fn run_repl(version: &str, runner: Runner) -> i32:
    let terminal = terminal_new()
    let editor = LineEditor::new(terminal)

    # Track prelude for definitions
    let mut prelude = String::new()

    # Handle input submission
    editor.on_submit(fn(input: String):
        if input.trim().is_empty():
            return

        # Check if definition
        let is_def = is_definition_like(&input)
        let code = build_source(&prelude, &input, is_def)

        # Execute
        match runner.run_source_in_memory(&code):
            case Ok(_):
                if is_def:
                    append_to_prelude(&mut prelude, &input, true)
            case Err(e):
                eprintln("Error: {}", e)
    )

    # Event loop
    let mut running = true
    while running:
        editor.render(&f"Simple v{version} >>> ")

        let event = read_event(100)
        if event.event_type == EventType::Key:
            if event.key_code == KEY_ESCAPE:
                running = false
            else:
                editor.handle_event(event)

    terminal_cleanup(terminal)
    return 0
```

### 5.3 FFI Bridge from Rust Driver

**File**: `src/runtime/src/value/repl.rs`

```rust
// Bridge to call Simple REPL from Rust driver

#[no_mangle]
pub extern "C" fn simple_repl_run(
    version: *const u8,
    version_len: usize,
    runner_handle: u64
) -> i32 {
    // Call into Simple: app::repl::run_repl(version, runner)
    // Return exit code
}
```

**File**: `src/driver/src/main.rs`

```rust
// Call Simple REPL
#[cfg(feature = "tui")]
if !use_notui {
    // Load Simple REPL application
    extern "C" {
        fn simple_repl_run(
            version: *const u8,
            version_len: usize,
            runner_handle: u64
        ) -> i32;
    }

    let version_bytes = version().as_bytes();
    let exit_code = unsafe {
        simple_repl_run(
            version_bytes.as_ptr(),
            version_bytes.len(),
            runner.as_handle()
        )
    };
    std::process::exit(exit_code);
}
```

---

## 6. Testing Strategy

### 6.1 Unit Tests

Test individual widgets in isolation:

```simple
# simple/std_lib/test/unit/ui/tui/line_editor_spec.spl

use spec.*
use ui.tui.widgets.line_editor.*

describe "LineEditor":
    context "smart backspace":
        it "deletes 4 spaces in leading whitespace":
            let editor = LineEditor::new_headless()  # Mock parent
            editor.set_text("    if 1:")
            editor.set_cursor(4)
            editor.handle_backspace()

            expect(editor.get_text()).to eq("")
            expect(editor.cursor_position()).to eq(0)

        it "deletes 1 character in normal text":
            let editor = LineEditor::new_headless()
            editor.set_text("hello")
            editor.set_cursor(5)
            editor.handle_backspace()

            expect(editor.get_text()).to eq("hell")
            expect(editor.cursor_position()).to eq(4)

    context "auto-indentation":
        it "adds 4 spaces after colon":
            let editor = LineEditor::new_headless()
            editor.set_text("if 1:")
            editor.handle_enter()

            expect(editor.get_text()).to eq("    ")
            expect(editor.cursor_position()).to eq(4)

    context "multiline mode":
        it "enters multiline on colon":
            let editor = LineEditor::new_headless()
            editor.set_text("if 1:")
            editor.handle_enter()

            expect(editor.is_multiline()).to be_true()

        it "exits multiline on empty line":
            let editor = LineEditor::new_headless()
            editor.set_text("if 1:")
            editor.handle_enter()
            editor.set_text("")
            let result = editor.handle_enter()

            expect(editor.is_multiline()).to be_false()
            expect(result).to be_some()
```

### 6.2 Integration Tests

Test Ratatui FFI bridge:

```simple
# simple/std_lib/test/integration/ui/tui/ratatui_backend_spec.spl

use spec.*
use ui.tui.backend.ratatui.*

describe "Ratatui Backend":
    context "terminal lifecycle":
        it "creates and cleans up terminal":
            let terminal = terminal_new()
            expect(terminal).to_not eq(0)

            terminal_cleanup(terminal)
            # Terminal destroyed

    context "text buffer operations":
        it "creates empty buffer":
            let buffer = textbuffer_new()
            expect(buffer).to_not eq(0)

            let text = textbuffer_get_text(buffer)
            expect(text).to eq("")

            object_destroy(buffer)

        it "inserts and gets text":
            let buffer = textbuffer_new()

            textbuffer_set_text(buffer, "Hello, World!")
            let text = textbuffer_get_text(buffer)

            expect(text).to eq("Hello, World!")

            object_destroy(buffer)

        it "handles backspace correctly":
            let buffer = textbuffer_new()
            textbuffer_set_text(buffer, "Hello")

            textbuffer_backspace(buffer)
            let text = textbuffer_get_text(buffer)

            expect(text).to eq("Hell")

            object_destroy(buffer)

    context "rendering":
        it "renders text buffer with prompt":
            let terminal = terminal_new()
            let buffer = textbuffer_new()

            textbuffer_set_text(buffer, "test input")
            render_textbuffer(terminal, buffer, ">>> ")

            # Check rendering completed without error

            object_destroy(buffer)
            terminal_cleanup(terminal)
```

### 6.3 System Tests

End-to-end REPL tests using PTY:

```rust
// src/driver/tests/simple_repl_e2e_test.rs

#[test]
fn test_simple_repl_basic_input() {
    let pty = portable_pty::PtySystem::default();
    let pair = pty.openpty(portable_pty::PtySize::default()).unwrap();

    let mut cmd = std::process::Command::new("./target/debug/simple");
    cmd.env("SIMPLE_REPL_BACKEND", "appcui");

    let child = pair.slave.spawn_command(cmd).unwrap();
    let mut reader = pair.master.try_clone_reader().unwrap();
    let mut writer = pair.master.take_writer().unwrap();

    // Wait for prompt
    wait_for_output(&mut reader, ">>> ");

    // Send input
    writer.write_all(b"1 + 2\n").unwrap();

    // Expect output
    let output = read_output(&mut reader, 1000);
    assert!(output.contains("3"));
}
```

---

## Summary

### Implementation Phases

**Phase 1: FFI Bridge** ✅ **COMPLETE**
- ✅ Added Ratatui dependencies (`ratatui = "0.28"`, `crossterm = "0.28"`)
- ✅ Implemented FFI functions in `src/runtime/src/value/ratatui_tui.rs` (630 lines)
- ✅ 13 FFI functions: terminal, text buffer, rendering, events
- ✅ Thread-safe architecture (`Send + Sync`)
- ✅ Build validation successful
- 📋 **Next**: Create Simple bindings in `simple/std_lib/src/ui/tui/backend/ratatui.spl`

**Phase 2: Widget Updates** (2-3 days)
- Update existing widgets to use Ratatui backend
- Implement LineEditor widget with TextBuffer
- Write unit tests for smart backspace and auto-indent

**Phase 3: REPL Application** (2-3 days)
- Create `simple/app/repl/` implementation
- Integrate with Rust driver
- Write system tests

**Total Estimate**: 6-9 days (Phase 1 complete, 4-6 days remaining)

### Benefits

1. ✅ **Thread-safe** (`Send + Sync`) - compatible with FFI architecture
2. ✅ **Modern TUI framework** - Ratatui 0.28 with active development
3. ✅ **Cross-platform** - Works on Windows, Linux, macOS via Crossterm
4. ✅ **REPL in Simple language** - Self-hosting goal
5. ✅ **Immediate-mode rendering** - Simple, efficient UI updates
6. ✅ **Rich ecosystem** - 10K+ stars, excellent documentation
7. ✅ **No thread safety issues** - Unlike AppCUI (`!Send`)

### Why Ratatui Over AppCUI?

**AppCUI Blocker** (discovered during Phase 1):
- ❌ Not `Send` - uses raw pointers (`*mut ()`, `NonNull<T>`)
- ❌ Incompatible with `static Mutex<HashMap<>>` FFI pattern
- ❌ Would require complex workarounds (thread-local storage, message passing)

**Ratatui Solution**:
- ✅ All types implement `Send + Sync`
- ✅ Works seamlessly with FFI architecture
- ✅ Modern, idiomatic Rust patterns
- ✅ Better documentation (vs AppCUI's 17% coverage)
- ✅ Active community (10K+ stars vs AppCUI's smaller community)

### Migration Path

1. ✅ **Phase 1 Complete** - Ratatui FFI bridge implemented and validated
2. Keep existing Rust TUI as fallback (`--notui` flag)
3. Implement Ratatui backend alongside current implementation
4. Switch REPL to Simple implementation gradually
5. Deprecate Rust TUI once Simple version is stable

### References

- [Ratatui](https://ratatui.rs/) - Official website
- [Ratatui GitHub](https://github.com/ratatui-org/ratatui) - 10K+ stars
- [Crossterm](https://github.com/crossterm-rs/crossterm) - Terminal backend
- [Implementation Report](../report/RATATUI_INTEGRATION_SUCCESS_2025-12-27.md) - Phase 1 completion details
- [Blocker Analysis](../../APPCUI_INTEGRATION_BLOCKERS.md) - Why AppCUI failed
