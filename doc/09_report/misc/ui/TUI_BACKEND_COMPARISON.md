# TUI Backend Comparison: AppCUI-rs vs Simple TUI Library

**Date**: 2025-12-27
**Context**: Evaluating backend options for Simple REPL TUI mode

## Executive Summary

We compare two approaches for the Simple REPL TUI:
1. **AppCUI-rs Backend**: Use AppCUI-rs as widget framework
2. **Simple TUI Library**: Use existing Simple TUI library with text-line interface

**Recommendation**: **Use Simple TUI Library** for line-based REPL, optionally integrate AppCUI-rs for future full-featured TUI applications.

---

## Current State

### Simple REPL (Rust, using crossterm)

**Location**: `src/driver/src/cli/tui/repl.rs`

**Crossterm Features Used**:
```rust
use crossterm::{
    cursor,                           // Cursor positioning
    event::{self, Event},            // Keyboard event reading
    execute, queue,                  // Rendering macros
    style::{Color, Print, SetForegroundColor, ResetColor},  // Colors
    terminal::{self, Clear, ClearType, enable_raw_mode, disable_raw_mode},
};
```

**Core Operations**:
1. **Terminal Setup**: `enable_raw_mode()`, `disable_raw_mode()`
2. **Event Handling**: `event::read()` for keyboard input
3. **Cursor Control**: `MoveToColumn()`, `Show`
4. **Screen Management**: `Clear(ClearType::CurrentLine)`
5. **Color Output**: `SetForegroundColor`, `ResetColor`
6. **Text Rendering**: `Print(text)`

**REPL Requirements**:
- Line-based input with cursor positioning
- Multi-line editing (Python-like)
- Auto-indentation after `:`
- Smart backspace (delete 4 spaces in leading whitespace)
- Colored prompt (`>>>` green, `...` green)
- Clear current line and redraw

### Simple TUI Library (Simple language)

**Location**: `simple/std_lib/src/ui/tui/`

**Current Widgets**:
- Menu (selectable items)
- Dialog (modal dialogs)
- ProgressBar
- TextInput (single-line with cursor)
- ScrollList (scrollable items)

**Backend**: Direct `libc` calls via `host.async_nogc_mut.io.term.*`
- Raw mode: `tcgetattr`, `tcsetattr`
- Terminal size: `ioctl(TIOCGWINSZ)`
- Screen buffer with dirty tracking
- Box-drawing characters
- ANSI color codes

**Architecture**:
```
TuiRenderer
  ├─ ScreenBuffer (cells with colors/styles)
  ├─ Terminal (raw mode, cursor, clear)
  ├─ Layout system
  └─ Widget rendering
```

---

## Approach 1: AppCUI-rs Backend

### What is AppCUI-rs?

**Source**: [GitHub](https://github.com/gdt050579/AppCUI-rs) | [Crates.io](https://crates.io/crates/appcui) | [Docs](https://docs.rs/appcui)

AppCUI-rs is a "fast, cross-platform console and text-based user interface (CUI/TUI) framework for Rust" with:
- **Rich Widget Library**: Buttons, labels, text boxes, checkboxes, radio buttons, list views, tree views, combo boxes, tabs, menus, toolbars, dialogs
- **Layout System**: Absolute, relative, docking, alignment, anchors, pivot positioning
- **Backend Abstraction**: Windows Console, Windows VT, NCurses, Termios, WebGL, **CrossTerm**
- **Features**: Mouse/keyboard/clipboard, 24-bit colors, Unicode, themes, multi-threading

### Integration Approach

**Option 1A: Use AppCUI-rs in Rust REPL**

```rust
// Replace crossterm with AppCUI
use appcui::{Application, TextBox, Window};

fn run_appcui_repl() {
    let mut app = Application::new()?;
    let window = Window::new("Simple REPL");
    let textbox = TextBox::new()
        .multiline(true)
        .syntax_highlighting(true);

    window.add_child(textbox);
    app.run();
}
```

**Pros**:
- Rich text editing out of the box
- Multi-line editing with scrolling
- Syntax highlighting capability
- Dialog support for errors
- Cross-platform tested

**Cons**:
- Heavy dependency (pulls in entire framework)
- Different architecture from current REPL
- Rust-only (can't use Simple TUI library)
- More complex than needed for line-based REPL
- Not leveraging existing Simple infrastructure

**Option 1B: AppCUI as backend for Simple TUI**

Make Simple TUI library call AppCUI via FFI instead of libc.

**Pros**:
- Unified TUI framework for all Simple apps
- Widget library for Simple language applications

**Cons**:
- Complex FFI bridge (Rust AppCUI ↔ Simple)
- Adds layer of abstraction
- Simple TUI already works with libc
- Increases compile times

---

## Approach 2: Simple TUI Library for REPL

### Architecture

Use existing Simple TUI library from Simple language to build REPL UI, bridge to Rust driver.

**Component Flow**:
```
Rust Driver (src/driver/src/main.rs)
      ↓ FFI call
Simple REPL App (simple/app/repl/main.spl)
      ↓ uses
Simple TUI Library (simple/std_lib/src/ui/tui/)
      ↓ uses
Terminal FFI (host.async_nogc_mut.io.term.*)
      ↓ calls
libc (tcsetattr, ioctl, etc.)
```

### Implementation Options

**Option 2A: Text-Line Widget for REPL**

Create a specialized `LineEditor` widget in Simple TUI library:

```simple
# simple/std_lib/src/ui/tui/line_editor.spl

pub struct LineEditor:
    id: NodeId
    lines: Array[String]
    current_line: String
    cursor: u64
    in_multiline: bool
    prompt_normal: String    # ">>> "
    prompt_continue: String  # "... "

impl LineEditor:
    pub fn new(id: NodeId) -> LineEditor:
        # ... initialization

    pub fn insert_char(self, ch: char):
        self.current_line.insert(self.cursor, ch)
        self.cursor += 1

    pub fn backspace(self):
        # Smart backspace: delete 4 spaces in leading whitespace
        let leading_spaces = self.current_line.chars()
            .take_while(|c| c == ' ')
            .count()

        if self.cursor <= leading_spaces and self.cursor >= 4:
            # Delete 4 spaces
            for _ in 0..4:
                self.cursor -= 1
                self.current_line.remove(self.cursor)
        else:
            # Delete 1 character
            if self.cursor > 0:
                self.cursor -= 1
                self.current_line.remove(self.cursor)

    pub fn accept_line(self):
        if self.current_line.trim_end().ends_with(':'):
            # Enter multiline mode
            self.lines.push(self.current_line.clone())
            self.in_multiline = true
            # Auto-indent
            let indent = self.calculate_indent(&self.current_line) + 4
            self.current_line = " ".repeat(indent)
            self.cursor = indent
        else if self.in_multiline:
            if self.current_line.trim().is_empty():
                # Exit multiline, return full input
                return Some(self.lines.join("\n"))
            else:
                self.lines.push(self.current_line.clone())
                let indent = self.calculate_indent(&self.current_line)
                self.current_line = " ".repeat(indent)
                self.cursor = indent
        else:
            # Single line complete
            return Some(self.current_line.clone())
        return None

    pub fn to_element(self, alloc: fn() -> NodeId) -> Element:
        let mut root = Element::new(self.id, ElementKind::Box)

        # Render completed lines
        for line in self.lines:
            let prompt = if line == self.lines[0] {
                &self.prompt_normal
            } else {
                &self.prompt_continue
            }
            let elem = Element::text(alloc(), &f"{prompt}{line}")
                .with_class("repl-line")
            root = root.with_child(elem)

        # Render current line with cursor
        let prompt = if self.in_multiline {
            &self.prompt_continue
        } else {
            &self.prompt_normal
        }
        let current_elem = Element::text(alloc(), &f"{prompt}{self.current_line}")
            .with_class("repl-current")
            .with_attr("cursor", &self.cursor.to_string())
        root = root.with_child(current_elem)

        return root
```

**Option 2B: Minimal Text-Only Interface**

Create a minimal FFI layer that exposes only what REPL needs:

```simple
# simple/std_lib/src/ui/tui/repl_io.spl

pub struct ReplTerminal:
    term: Terminal

impl ReplTerminal:
    pub async fn new() -> ReplTerminal:
        let term = Terminal::default().await
        term.enable_raw_mode().await.unwrap()
        return ReplTerminal { term: term }

    pub async fn read_key(self) -> Key:
        return self.term.read_key().await

    pub async fn render_line(self, prompt: &str, text: &str, cursor: u64):
        self.term.move_to_column(0).await
        self.term.clear_line().await
        self.term.set_fg_color(Color::Green).await
        self.term.print(prompt).await
        self.term.reset_color().await
        self.term.print(text).await
        self.term.move_to_column((prompt.len() + cursor) as u16).await
        self.term.flush().await

    pub async fn print_line(self, text: &str):
        self.term.print(text).await
        self.term.print("\r\n").await

    pub fn disable_raw_mode(self):
        self.term.disable_raw_mode().await.unwrap()
```

**Rust FFI Bridge**:
```rust
// src/runtime/src/value/tui_repl.rs

#[no_mangle]
pub extern "C" fn simple_repl_terminal_new() -> u64 {
    // Create ReplTerminal instance via Simple interpreter
    // Return handle
}

#[no_mangle]
pub extern "C" fn simple_repl_read_key(handle: u64) -> u64 {
    // Call Simple async function, return key code
}

#[no_mangle]
pub extern "C" fn simple_repl_render_line(
    handle: u64,
    prompt: *const u8,
    text: *const u8,
    cursor: u64
) {
    // Call Simple async function
}
```

---

## Comparison Matrix

| Feature | Current (crossterm) | AppCUI-rs | Simple TUI + Widget | Simple TUI Minimal |
|---------|---------------------|-----------|---------------------|---------------------|
| **Dependency Weight** | Medium (crossterm) | Heavy (AppCUI) | None (Simple stdlib) | None (Simple stdlib) |
| **Implementation Language** | Rust | Rust | Simple + Rust FFI | Simple + Rust FFI |
| **Line Editing** | Custom (272 LOC) | Built-in | Custom (150 LOC) | Custom (100 LOC) |
| **Multi-line Support** | ✅ Custom | ✅ Built-in | ✅ Custom | ✅ Custom |
| **Auto-indent** | ✅ Custom | ⚠️ Need config | ✅ Custom | ✅ Custom |
| **Smart Backspace** | ✅ Custom | ⚠️ Need config | ✅ Custom | ✅ Custom |
| **Colored Prompts** | ✅ | ✅ | ✅ | ✅ |
| **Widget Reuse** | ❌ | ✅ (Rust only) | ✅ (Simple apps) | ❌ |
| **Complexity** | Low | High | Medium | Low |
| **Testability** | Easy (PTY) | Medium | Easy (Simple tests) | Easy (Simple tests) |
| **Cross-platform** | ✅ | ✅ | ✅ (libc) | ✅ (libc) |
| **Future TUI Apps** | N/A | ✅ (Rust) | ✅ (Simple) | ❌ |
| **Maintenance Burden** | Low | Medium | Low (Simple) | Low (Simple) |
| **Learning Curve** | Low | High | Medium | Low |
| **Build Time Impact** | +2s | +5s | 0s | 0s |

---

## Crossterm Usage Analysis

### What Simple REPL Actually Needs

From `src/driver/src/cli/tui/repl.rs`:

```rust
// Essential operations (used frequently)
terminal::enable_raw_mode()       // Setup
terminal::disable_raw_mode()      // Cleanup
event::read() -> Event::Key       // Main event loop
cursor::MoveToColumn(n)           // Cursor positioning
Clear(ClearType::CurrentLine)     // Erase line
SetForegroundColor(Color::Green)  // Prompt color
Print(text)                       // Output
stdout.flush()                    // Render

// Nice-to-have (used occasionally)
cursor::Show                      // Cursor visibility
ResetColor                        // Color reset
```

**Minimal API Surface**: ~10 operations total

**Simple TUI Equivalent**:
```simple
Terminal::enable_raw_mode()      // ✅ Implemented
Terminal::disable_raw_mode()     // ✅ Implemented
Terminal::read_key()              // ✅ Implemented
Terminal::move_to_column(n)       // ✅ Implemented
Terminal::clear_line()            // ✅ Implemented
Terminal::set_fg_color(color)     // ✅ Implemented
Terminal::print(text)             // ✅ Implemented
Terminal::flush()                 // ✅ Implemented
Terminal::show_cursor()           // ✅ Implemented
Terminal::reset_color()           // ✅ Implemented
```

**All operations already implemented in Simple TUI library!**

---

## Recommendations

### For Simple REPL

**Use Approach 2B: Simple TUI Minimal Interface**

**Why**:
1. ✅ **Zero additional dependencies** - uses existing Simple stdlib
2. ✅ **All required operations exist** - no new code needed in TUI library
3. ✅ **Simpler architecture** - direct FFI calls, no complex bridges
4. ✅ **Testable in Simple** - can write BDD tests for REPL logic
5. ✅ **Self-hosting** - REPL implementation in Simple language
6. ✅ **Fast builds** - no heavyweight dependencies
7. ✅ **Learning opportunity** - showcases Simple language capabilities

**Implementation Plan**:

1. **Create `simple/app/repl/main.spl`** (new REPL implementation in Simple)
   - Use `host.async_nogc_mut.io.term.*` for terminal control
   - Implement LineEditor logic in Simple
   - Handle keyboard events and rendering

2. **Create FFI bridge in `src/runtime/src/value/repl.rs`**
   - Expose Simple REPL to Rust driver
   - Marshal keyboard events and output

3. **Update `src/driver/src/main.rs`**
   - Call Simple REPL via FFI instead of Rust TUI
   - Pass version, runner handle

4. **Keep existing Rust TUI as fallback**
   - Use `--notui` for old Normal mode
   - Use `--tui-rust` for current Rust TUI (debugging)

**Estimated Effort**: 2-3 days
- Day 1: `repl/main.spl` with LineEditor logic
- Day 2: FFI bridge and integration
- Day 3: Testing and polish

### For Future Full TUI Apps

**Consider AppCUI-rs for Rust-based TUI tools**

If building complex TUI applications in Rust (like debugger, file browser), AppCUI-rs provides:
- Rich widget library
- Event system
- Layout engine
- Dialog system

**Use Simple TUI Library for Simple-based TUI apps**

For applications written in Simple language, the existing TUI library provides:
- Native integration
- Widget system (Menu, Dialog, ProgressBar, ScrollList)
- Element-based rendering
- Theme support via CSS-like classes

---

## Conclusion

**Best Approach**: **Simple TUI Library with Minimal Text-Only Interface (2B)**

**Rationale**:
1. All required terminal operations already exist in Simple stdlib
2. Zero additional Rust dependencies
3. Self-hosting - REPL in Simple language
4. Leverages existing infrastructure
5. Educational value - demonstrates Simple language maturity
6. Easier to test (BDD in Simple)
7. Faster builds, simpler architecture

**AppCUI-rs verdict**: Excellent library, but **overkill for line-based REPL**. Consider for future complex Rust TUI applications (debugger, profiler, file browser).

**Simple TUI Library**: Perfect fit for REPL and future Simple language TUI applications.

---

## Next Steps

1. ✅ Commit current TUI changes to jj
2. Create `simple/app/repl/` directory structure
3. Implement `LineEditor` in Simple with all current features
4. Create FFI bridge for Rust ↔ Simple REPL
5. Update driver to call Simple REPL
6. Write BDD tests for REPL logic
7. Document Simple REPL architecture

---

## References

- [AppCUI-rs GitHub](https://github.com/gdt050579/AppCUI-rs)
- [AppCUI-rs Crates.io](https://crates.io/crates/appcui)
- [AppCUI-rs Documentation](https://docs.rs/appcui)
- [Ratatui](https://ratatui.rs/) - Alternative TUI framework
- Current REPL: `src/driver/src/cli/tui/repl.rs`
- Simple TUI: `simple/std_lib/src/ui/tui/`
