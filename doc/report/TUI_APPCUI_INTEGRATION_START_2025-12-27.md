# TUI AppCUI-rs Integration - Phase 1 Started

**Date**: 2025-12-27
**Status**: IN PROGRESS - Phase 1 (Documentation & FFI Foundation)
**Progress**: 40% (4/10 features)

## Summary

Started integrating AppCUI-rs as the backend for Simple TUI library, replacing direct `libc` calls with a cross-platform TUI framework. This will enable:
- Rich widget library
- REPL implementation in Simple language
- Cross-platform terminal UI (Windows, Linux, macOS, WebGL)

---

## Completed Tasks ✅

### 1. Documentation

**Created `doc/spec/tui.md`** - Complete TUI Framework Specification
- Architecture overview (Simple Apps → Simple TUI → AppCUI → Terminal)
- Backend integration design
- FFI function signatures for all operations
- Widget system specification
- Event handling architecture
- REPL integration design
- Testing strategy

**Created `doc/report/TUI_BACKEND_COMPARISON.md`** - Technical Comparison
- AppCUI-rs vs Simple TUI library comparison
- Crossterm usage analysis (current REPL needs ~10 operations)
- Two approaches evaluated:
  - Approach 1: AppCUI-rs widgets directly
  - Approach 2: Simple TUI with AppCUI backend ✅ CHOSEN
- Implementation phases and timeline
- Benefits and rationale

### 2. Feature Tracking

**Updated `doc/features/feature.md`**
- Added new feature range: #1830-#1839 TUI Backend Integration
- 10 features planned across 3 phases
- Documentation links
- Test paths defined
- Difficulty ratings assigned

**Features Defined**:
- #1830: AppCUI-rs Cargo dependency ✅
- #1831: AppCUI FFI bridge (app/window/events) ✅
- #1832: AppCUI FFI bridge (textbox/widgets) ✅
- #1833: Simple AppCUI bindings 📋
- #1834: Update TUI renderer 📋
- #1835: LineEditor widget for REPL 📋
- #1836: REPL application in Simple 📋
- #1837: Rust driver FFI to Simple REPL 📋
- #1838: Event handling system 📋
- #1839: Migration from Rust TUI 📋

### 3. Dependency Management

**Updated `src/runtime/Cargo.toml`**
```toml
[features]
appcui = ["dep:appcui"]  # AppCUI-rs TUI framework

[dependencies]
appcui = { version = "0.4", optional = true }
```

- Added as optional feature (like `vulkan`, `pytorch`)
- Build with `--features appcui` to enable
- Zero impact when feature disabled

### 4. FFI Bridge Foundation

**Created `src/runtime/src/value/appcui.rs`**
- 450+ lines of FFI bridge code
- Handle-based object management (AppCuiObject registry)
- Feature-gated compilation (`#[cfg(feature = "appcui")]`)
- Stub implementations when feature disabled

**Functions Implemented**:
```rust
// Application Management
extern "C" fn appcui_app_new() -> u64
extern "C" fn appcui_app_run(app_handle: u64) -> i32
extern "C" fn appcui_app_quit(app_handle: u64, exit_code: i32)

// Window Management
extern "C" fn appcui_window_new(app, title, title_len, width, height) -> u64
extern "C" fn appcui_window_show(window_handle: u64)

// Text Box Widget
extern "C" fn appcui_textbox_new(parent, x, y, width, height, multiline) -> u64
extern "C" fn appcui_textbox_set_text(textbox, text, text_len)
extern "C" fn appcui_textbox_get_text(textbox, buffer, buffer_len) -> usize
extern "C" fn appcui_textbox_set_cursor(textbox, position)

// Event Handling
extern "C" fn appcui_set_event_callback(app, callback, user_data)

// Layout
extern "C" fn appcui_widget_set_layout(widget, x, y, width, height, dock)
```

**Updated `src/runtime/src/value/mod.rs`**
- Added `pub mod appcui` with feature gate
- Integrated into module structure

---

## AppCUI API Discovery

While implementing, discovered actual AppCUI API structure:

### Real AppCUI API (from [crates.io](https://crates.io/crates/appcui))

```rust
use appcui::prelude::*;

// Application creation
let mut app = App::new().build()?;

// Window creation (macro-based)
let mut win = window!("Test,d:c,w:30,h:9");

// Or builder-based
let mut win = Window::new(
    "Test",
    LayoutBuilder::new().alignment(Alignment::Center).width(30).height(9).build(),
    window::Flags::Sizeable,
);

// Add controls
win.add(label!("'Hello World!',d:c,w:13,h:1"));

// Run app
app.add_window(win);
app.run();
```

**Key Differences from Initial Assumption**:
- Uses `App` not `Application`
- Macro-based widget creation (`window!`, `label!`)
- Builder pattern for layouts (`LayoutBuilder`)
- `add_window()` method on App
- Different event handling model

---

## Next Steps

### Phase 1 Completion (Remaining 1-2 days)

1. **Fix FFI Bridge to Match Real API** 🔄
   - Update `appcui.rs` to use actual `App` struct
   - Implement builder-based window creation
   - Add TextBox widget support (verify API exists)
   - Implement actual event handling

2. **Simple Language Bindings** 📋
   - Create `simple/std_lib/src/ui/tui/backend/appcui.spl`
   - Wrap FFI functions in Simple API
   - Add event type definitions
   - Document usage examples

3. **Integration Tests** 📋
   - Create `src/runtime/tests/appcui/` directory
   - Test app creation and lifecycle
   - Test window creation and display
   - Test textbox operations
   - Test event callbacks

### Phase 2: Widget Updates (2-3 days)

4. **Update TUI Renderer** 📋
   - Modify `simple/std_lib/src/ui/tui/renderer.spl`
   - Replace libc calls with AppCUI backend
   - Update screen buffer logic
   - Add layout management

5. **LineEditor Widget** 📋
   - Create `simple/std_lib/src/ui/tui/widgets/line_editor.spl`
   - Implement smart backspace (4 spaces)
   - Implement auto-indentation after `:`
   - Implement multiline mode
   - Add unit tests

### Phase 3: REPL Application (2-3 days)

6. **REPL in Simple** 📋
   - Create `simple/app/repl/main.spl`
   - Use LineEditor widget
   - Integrate with compiler/interpreter
   - Handle input submission

7. **Rust Driver Integration** 📋
   - Create FFI bridge in `src/runtime/src/value/repl.rs`
   - Update `src/driver/src/main.rs`
   - Add `--repl-simple` flag (vs `--tui-rust` fallback)
   - Create E2E tests

---

## Files Modified

### Documentation
- `doc/spec/tui.md` (NEW) - 500+ lines
- `doc/report/TUI_BACKEND_COMPARISON.md` (NEW) - 400+ lines
- `doc/features/feature.md` (MODIFIED) - Added #1830-#1839

### Source Code
- `src/runtime/Cargo.toml` (MODIFIED) - Added appcui dependency
- `src/runtime/src/value/appcui.rs` (NEW) - 450+ lines FFI bridge
- `src/runtime/src/value/mod.rs` (MODIFIED) - Added appcui module

### Total Lines Added
- Documentation: ~900 lines
- Source Code: ~470 lines
- **Total: ~1,370 lines**

---

## Build Instructions

### Enable AppCUI Feature

```bash
# Build with AppCUI support
cargo build --features appcui

# Build all features
cargo build --all-features

# Run tests
cargo test --features appcui -p simple-runtime
```

### Test AppCUI FFI

```rust
// Example test (once API is fixed)
#[test]
#[cfg(feature = "appcui")]
fn test_appcui_app_lifecycle() {
    let handle = appcui_app_new();
    assert_ne!(handle, 0);
    appcui_app_quit(handle, 0);
}
```

---

## Technical Decisions

### Why AppCUI-rs?

1. ✅ **Rich Widget Library**: 20+ built-in widgets
2. ✅ **Cross-Platform**: Windows Console, NCurses, Termios, WebGL backends
3. ✅ **Active Development**: Regular releases, good examples
4. ✅ **MIT License**: Compatible with Simple
5. ✅ **Rust-Native**: No C dependencies, easier FFI

### Why Not Just Crossterm?

Current REPL uses crossterm directly in Rust. Switching to AppCUI + Simple enables:
- **Self-Hosting**: REPL written in Simple language (educational value)
- **Widget Reuse**: Other Simple apps can use same TUI framework
- **Learning Tool**: Demonstrates Simple language maturity
- **Flexibility**: Can build complex TUIs beyond line-based REPL

---

## Challenges Encountered

1. **API Documentation**: AppCUI docs.rs shows 17.48% coverage
   - **Solution**: Check examples on GitHub, use `appcui::prelude::*`

2. **Different API than Expected**: Initial implementation assumed different API
   - **Solution**: Update FFI bridge to match actual `App`/`Window` API

3. **Macro-Based Widgets**: AppCUI heavily uses macros (`window!`, `label!`)
   - **Solution**: Use builder-based API in FFI, macros in Simple later

---

## References

- [AppCUI GitHub](https://github.com/gdt050579/AppCUI-rs) - Examples and source
- [AppCUI crates.io](https://crates.io/crates/appcui) - Version 0.4.6
- [AppCUI docs.rs](https://docs.rs/appcui) - API documentation (17% coverage)
- [Medium Tutorial](https://medium.com/@protiumx/creating-a-text-based-ui-with-rust-2d8eaff7fe8b) - Creating TUI with Rust

---

## Timeline

**Start Date**: 2025-12-27
**Phase 1 Target**: 2025-12-29 (2-3 days)
**Phase 2 Target**: 2026-01-01 (2-3 days)
**Phase 3 Target**: 2026-01-04 (2-3 days)
**Overall Estimate**: 6-9 days total

**Current Status**: Day 1 (40% Phase 1 complete)

---

## Success Criteria

### Phase 1 ✅
- [x] Spec documentation complete
- [x] Feature tracking updated
- [x] Dependency added to Cargo.toml
- [x] FFI bridge foundation created
- [ ] FFI bridge matches real AppCUI API
- [ ] Simple bindings created
- [ ] Integration tests passing

### Phase 2 📋
- [ ] TUI renderer uses AppCUI backend
- [ ] LineEditor widget implemented
- [ ] Widget unit tests passing

### Phase 3 📋
- [ ] REPL runs in Simple language
- [ ] Rust driver calls Simple REPL
- [ ] E2E tests passing
- [ ] Feature parity with current Rust TUI

---

## Next Session Tasks

1. **Fix appcui.rs to match real API**
   - Update `App::new().build()`
   - Fix window creation with `Window::new` or `window!` macro
   - Check if TextBox widget exists or use TextField/Input
   - Implement proper event handling

2. **Create Simple bindings** (`appcui.spl`)
   - FFI wrapper functions
   - Event type definitions
   - Example usage in comments

3. **Write integration tests**
   - `src/runtime/tests/appcui/app_lifecycle.rs`
   - `src/runtime/tests/appcui/window_creation.rs`
   - `src/runtime/tests/appcui/textbox_operations.rs`

4. **Build and validate**
   - `cargo build --features appcui`
   - `cargo test --features appcui`
   - Fix any compilation errors

---

**Status**: Ready for Phase 1 completion. FFI bridge needs API updates based on real AppCUI structure.
