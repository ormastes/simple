# TUI Integration Phase 1 - Blocker Discovered

**Date**: 2025-12-27
**Status**: ⚠️ BLOCKED - Critical architectural incompatibility
**Progress**: 50% Phase 1 (5/10 features, but blocked)

---

## Summary

Phase 1 implementation discovered a **critical blocker**: AppCUI-rs is **not thread-safe** (`!Send`), which is incompatible with our FFI bridge architecture.

---

## What We Accomplished ✅

### 1. Complete Documentation (~1,250 lines)
- ✅ TUI framework specification (`doc/06_spec/tui.md`)
- ✅ Backend comparison analysis (`doc/09_report/TUI_BACKEND_COMPARISON.md`)
- ✅ Feature tracking (#1830-#1839 in `feature.md`)
- ✅ Progress tracking documents

### 2. FFI Bridge Foundation (~500 lines)
- ✅ Added `appcui = "0.4"` dependency to `Cargo.toml`
- ✅ Created `src/runtime/src/value/appcui.rs` (500 lines)
- ✅ 11 FFI functions defined
- ✅ Handle-based object management system
- ⚠️ **Does not compile** - thread safety issues

### 3. API Research
- ✅ Investigated real AppCUI API structure
- ✅ Discovered: `App::new().build()` (not `Application`)
- ✅ Discovered: `TextField` widget (not `TextBox`)
- ✅ Discovered: Builder pattern for layouts
- ⚠️ **Discovered: AppCUI is not `Send`**

---

## The Blocker 🚫

### Thread Safety Issue

```
error[E0277]: `*mut ()` cannot be sent between threads safely
  --> src/runtime/src/value/appcui.rs:26:25
   |
26 | static HANDLE_REGISTRY: Mutex<Option<HashMap<u64, AppCuiObject>>> = ...
   |                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |                         `*mut ()` cannot be sent between threads safely
```

**Root Cause**: AppCUI uses raw pointers internally (`*mut ()`, `NonNull<T>`) and is designed for **single-threaded** use only.

**Impact**: Our FFI bridge architecture requires `Send` types to store objects in a global `Mutex`-protected registry.

### Why This Matters

AppCUI is designed to run entirely on the **main UI thread**. All widgets, windows, and the app itself must be created and manipulated from the same thread. This conflicts with:

1. **FFI calling from Simple** - Simple code may run on different threads
2. **Global handle registry** - Requires `Send` to be thread-safe
3. **Rust safety guarantees** - Compiler won't allow non-`Send` types in static `Mutex`

---

## Options Forward

See `APPCUI_INTEGRATION_BLOCKERS.md` for detailed analysis.

### Option 1: Thread-Local Storage

**Approach**: Use `thread_local!` instead of `static Mutex`

```rust
thread_local! {
    static HANDLE_REGISTRY: RefCell<HashMap<u64, AppCuiObject>> = ...;
}
```

**Pros**:
- ✅ Works with non-Send types
- ✅ Minimal code changes

**Cons**:
- ❌ All FFI calls must come from same thread
- ❌ Simple code must run on UI thread
- ❌ Complex to enforce at runtime
- ❌ Runtime panics if violated

**Verdict**: ⚠️ Fragile, error-prone

### Option 2: Single-Thread Executor

**Approach**: Dedicated UI thread with message passing

```rust
// Main thread
let (tx, rx) = channel();
thread::spawn(move || {
    // All AppCUI operations here
});

// FFI sends commands
extern "C" fn appcui_app_new() -> u64 {
    tx.send(Command::CreateApp).unwrap();
    rx.recv().unwrap()
}
```

**Pros**:
- ✅ Proper thread isolation
- ✅ Enforces single-thread constraint

**Cons**:
- ❌ Very complex architecture
- ❌ Async/channel overhead
- ❌ Difficult to debug
- ❌ 3-4 days additional work

**Verdict**: ⚠️ Over-engineered for REPL

### Option 3: Direct API (No Handles)

**Approach**: Call AppCUI directly from Simple, no handle abstraction

**Pros**:
- ✅ Simpler
- ✅ No cross-thread issues

**Cons**:
- ❌ Simple code must run on UI thread
- ❌ Less flexible
- ❌ Tight coupling

**Verdict**: ⚠️ Limits Simple's concurrency model

### Option 4: Switch to Ratatui ⭐ RECOMMENDED

**Approach**: Use Ratatui instead of AppCUI

**Ratatui**: https://ratatui.rs/

**Why Ratatui**:
- ✅ **Implements `Send` + `Sync`** - thread-safe by design
- ✅ Rich widget library (similar to AppCUI)
- ✅ Active development (20+ contributors, 10K+ stars)
- ✅ Production-ready (used by many popular CLI tools)
- ✅ Excellent documentation and examples
- ✅ Compatible with crossterm (our current REPL already uses it!)
- ✅ Modern, idiomatic Rust
- ✅ No thread safety issues

**API Comparison**:

```rust
// AppCUI (!Send)
let mut app = App::new().build()?;  // Not Send
let window = Window::new(...);       // Not Send

// Ratatui (Send + Sync)
let mut terminal = Terminal::new(CrosstermBackend::new(stdout()))?;  // Send + Sync
terminal.draw(|f| {
    let block = Block::default().title("Simple REPL");
    f.render_widget(block, f.size());
})?;
```

**Migration Effort**: ~2 days
- Day 1: Update FFI bridge for Ratatui API
- Day 2: Update Simple bindings, basic tests

**Verdict**: ✅ **RECOMMENDED** - Clean, modern, no blockers

### Option 5: Keep Current Architecture

**Approach**: Stick with current crossterm-based Rust TUI

**Pros**:
- ✅ Already working
- ✅ No integration complexity
- ✅ Well-tested

**Cons**:
- ❌ REPL not in Simple language (not self-hosting)
- ❌ Misses educational value
- ❌ No reusable TUI framework for Simple apps

**Verdict**: ⚠️ Safe fallback, but loses self-hosting goal

---

## Recommendation

**Switch to Ratatui** (Option 4)

### Why?

1. **No thread safety issues** - Ratatui is `Send` + `Sync`
2. **Better fit** - Designed for modern Rust patterns
3. **Active ecosystem** - Well-maintained, good docs
4. **Crossterm compatible** - Works with our existing infrastructure
5. **2-day migration** - Same timeline as fixing AppCUI issues
6. **Future-proof** - Won't hit more thread safety walls

### Action Plan

**Phase 1 (Revised) - 2 days**:
1. Remove AppCUI dependency
2. Add Ratatui (`ratatui = "0.28"`)
3. Rewrite FFI bridge for Ratatui API
4. Update spec docs (replace AppCUI → Ratatui)
5. Basic integration tests

**Phase 2 - 2-3 days**:
6. Simple language bindings
7. LineEditor widget
8. TUI renderer updates

**Phase 3 - 2-3 days**:
9. REPL in Simple
10. Rust driver integration
11. E2E tests

**Total**: Still 6-9 days (same as original estimate)

---

## Files Modified This Session

### Documentation
- `doc/06_spec/tui.md` (NEW, 500+ lines)
- `doc/09_report/TUI_BACKEND_COMPARISON.md` (NEW, 400+ lines)
- `doc/09_report/TUI_APPCUI_INTEGRATION_START_2025-12-27.md` (NEW, 350+ lines)
- `doc/09_report/TUI_PHASE1_BLOCKER_2025-12-27.md` (NEW, this file)
- `APPCUI_INTEGRATION_BLOCKERS.md` (NEW, 150+ lines)
- `doc/features/feature.md` (MODIFIED, +40 lines)

### Source Code
- `src/runtime/Cargo.toml` (MODIFIED, +3 lines - appcui dependency)
- `src/runtime/src/value/appcui.rs` (NEW, 500 lines - **DOES NOT COMPILE**)
- `src/runtime/src/value/mod.rs` (MODIFIED, +2 lines)

**Total Lines**: ~2,000 lines (1,450 docs + 500 code + 50 config)

---

## Next Session

### Decision Required

**Question**: Do we switch to Ratatui or adapt our architecture for AppCUI?

**Recommended Answer**: Switch to Ratatui

### If Switching to Ratatui

1. Remove AppCUI dependency
2. Add `ratatui = "0.28"` to `Cargo.toml`
3. Research Ratatui API (widgets, layout, events)
4. Rewrite `src/runtime/src/value/tui.rs` (rename from appcui.rs)
5. Update all documentation (s/AppCUI/Ratatui/)
6. Continue with Phase 1

**Estimated Time**: 2 days to get back to where we are now, but **compilable**

---

## Lessons Learned

1. ✅ **Research API first** - Should have checked `Send` trait before committing
2. ✅ **Compile early** - Discovered blocker only after 500 lines written
3. ✅ **Thread safety matters** - FFI + static storage requires `Send`
4. ✅ **Modern Rust patterns** - Ratatui follows modern idioms, AppCUI uses older patterns

---

## References

- [AppCUI GitHub](https://github.com/gdt050579/AppCUI-rs) - Single-threaded TUI framework
- [Ratatui](https://ratatui.rs/) - Modern, thread-safe TUI framework ⭐
- [Ratatui GitHub](https://github.com/ratatui-org/ratatui) - 10K+ stars
- [Cursive](https://github.com/gyscos/cursive) - Alternative thread-safe TUI
- [Crossterm](https://github.com/crossterm-rs/crossterm) - Our current backend

---

**Status**: Ready for decision and pivot to Ratatui 🚀
