# AppCUI Integration Blockers

**Date**: 2025-12-27
**Status**: BLOCKED - Architecture incompatibility

## Critical Issue: Thread Safety

AppCUI objects (`App`, `Window`, `TextField`) **do not implement `Send`**, which means they cannot be safely sent between threads. This fundamentally conflicts with our FFI bridge architecture.

### Error Messages

```
error[E0277]: `*mut ()` cannot be sent between threads safely
  --> src/runtime/src/value/appcui.rs:26:25
   |
26 | static HANDLE_REGISTRY: Mutex<Option<HashMap<u64, AppCuiObject>>> = Mutex::new(None);
   |                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ `*mut ()` cannot be sent between threads safely
   |
   = help: within `appcui::prelude::App`, the trait `Send` is not implemented for `*mut ()`

error[E0277]: `NonNull<toolbar::toolbar::ToolBar>` cannot be sent between threads safely
```

### Root Cause

AppCUI is designed to run on a single thread (the main UI thread). It uses raw pointers internally (`*mut ()`, `NonNull<T>`) which are not thread-safe.

Our FFI bridge uses:
```rust
static HANDLE_REGISTRY: Mutex<Option<HashMap<u64, AppCuiObject>>> = Mutex::new(None);
```

This requires `AppCuiObject` to be `Send`, but AppCUI types are not.

## Alternative Approaches

### Option 1: Thread-Local Storage (Recommended Short-Term)

Use `thread_local!` instead of `static`:

```rust
thread_local! {
    static HANDLE_REGISTRY: RefCell<HashMap<u64, AppCuiObject>> = RefCell::new(HashMap::new());
}
```

**Pros**: Works with non-Send types
**Cons**: FFI must be called from the same thread that created objects

### Option 2: Single-Thread Executor

Run all AppCUI operations on a dedicated thread:

```rust
// Main thread spawns AppCUI thread
let (tx, rx) = channel();
thread::spawn(move || {
    // All AppCUI operations happen here
    let app = App::new().build().unwrap();
    // ...
});

// FFI sends commands via channel
extern "C" fn appcui_app_new() -> u64 {
    tx.send(Command::CreateApp).unwrap();
    rx.recv().unwrap()  // Wait for handle
}
```

**Pros**: Proper thread isolation
**Cons**: Complex, requires message passing, async complexity

### Option 3: Direct API (No Handle Abstraction)

Don't use handles - call AppCUI directly from Simple language:

```simple
# simple/std_lib/src/ui/tui/backend/appcui_direct.spl

use ffi

fn create_app() -> AppHandle:
    # Calls Rust which creates App and stores in TLS
    return ffi.call_direct("appcui_create_app_direct")

fn run_app(app: AppHandle):
    # Must be called from same thread
    ffi.call_direct("appcui_run_app_direct", app)
```

**Pros**: Simpler, no cross-thread issues
**Cons**: Simple code must run on same thread as AppCUI

### Option 4: Use Different TUI Library

Switch to a `Send`-compatible TUI library:

- **ratatui** (formerly tui-rs) - Implements `Send` for all types
- **cursive** - Thread-safe by design
- **crossterm** (current REPL) - Already using, `Send`-compatible

**Pros**: No thread safety issues
**Cons**: Less feature-rich than AppCUI, would need to rewrite integration

## Recommendation

**Short-term (Phase 1 completion)**: Switch to **Option 4 - Use Ratatui** instead of AppCUI

**Rationale**:
1. ✅ Ratatui is `Send` + `Sync` - works with our FFI architecture
2. ✅ Active development (20+ contributors)
3. ✅ Rich widget library (similar to AppCUI)
4. ✅ Good documentation and examples
5. ✅ Already compatible with crossterm (our current REPL uses it)
6. ✅ Production-ready (used by many CLI tools)

**Alternative**: Keep current crossterm-based Rust TUI, implement Simple TUI using crossterm directly (no AppCUI/ratatui), focus on REPL in Simple language.

## Next Steps

### Decision Required

1. **Continue with AppCUI** - Requires thread-local approach (Option 1 or 2)
2. **Switch to Ratatui** - Recommended, no thread safety issues
3. **Keep current architecture** - Crossterm + Rust TUI, Simple REPL uses crossterm FFI

### If Continuing with AppCUI (Thread-Local)

1. Replace `static Mutex` with `thread_local! RefCell`
2. Add thread ID checks in all FFI functions
3. Document that all calls must come from same thread
4. Add runtime panics if called from wrong thread

### If Switching to Ratatui

1. Update `Cargo.toml`: `ratatui = "0.28"`
2. Rewrite FFI bridge for ratatui API
3. Update spec to reference ratatui instead of AppCUI
4. Continue with Simple bindings and REPL implementation

## References

- [AppCUI GitHub](https://github.com/gdt050579/AppCUI-rs)
- [Ratatui](https://ratatui.rs/) - Modern, Send-compatible TUI framework
- [Cursive](https://github.com/gyscos/cursive) - Alternative TUI framework
- [Crossterm](https://github.com/crossterm-rs/crossterm) - Current REPL backend

---

**Decision Point**: Do we adapt our architecture to AppCUI's single-thread model, or switch to a Send-compatible library like Ratatui?
