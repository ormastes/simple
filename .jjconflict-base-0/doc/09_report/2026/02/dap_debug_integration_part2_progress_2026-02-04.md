# DAP Debug Integration - Part 2 Progress Report
**Date:** 2026-02-04
**Status:** 🔄 In Progress (Phase 2.1 Complete, Phase 2.2 Started)
**Part:** MCP/LSP/DAP Integration Plan - Part 2

---

## Summary

Implementing DAP (Debug Adapter Protocol) integration for the Simple runtime. Part 2 focuses on adding debug state infrastructure, interpreter hooks, and stack/variable capture to enable breakpoint debugging with step modes.

## Progress Overview

### ✅ Phase 2.1: Rust Debug State Infrastructure (Complete)

**Implemented:**
1. **Debug State Struct** (`build/src/bootstrap_ffi_debug.rs`)
   - `DebugState`: Global state with breakpoints, step mode, location tracking
   - `StepMode` enum: Continue, StepOver, StepIn, StepOut
   - `BreakpointInfo`: Breakpoint metadata with conditions and hit counts
   - `StackFrameInfo`: Stack frame tracking

2. **Global State Management**
   - `Mutex<DebugState>`: Thread-safe global debug state
   - Thread-local storage for stack frames and variables
   - `STACK_FRAMES`: Per-thread call stack
   - `LOCAL_VARS`: Thread-local variable map
   - `GLOBAL_VARS`: Thread-local global variable map

3. **FFI Functions** (30+ functions implemented)

**Basic State:**
- `rt_debug_is_active()` / `rt_debug_set_active()`
- `rt_debug_set_step_mode()` / `rt_debug_get_step_mode()`
- `rt_debug_set_step_start_depth()` / `rt_debug_get_step_start_depth()`

**Pause/Continue:**
- `rt_debug_pause()` / `rt_debug_continue()`
- `rt_debug_is_paused()`
- `rt_debug_wait_for_continue()` - Polling loop with 10ms sleep

**Location Tracking:**
- `rt_debug_set_current_location(file, line, column)`
- `rt_debug_current_file()` / `rt_debug_current_line()` / `rt_debug_current_column()`

**Breakpoints:**
- `rt_debug_add_breakpoint(file, line, id)`
- `rt_debug_remove_breakpoint(file, line)`
- `rt_debug_clear_breakpoints()`
- `rt_debug_has_breakpoint(file, line)`

**Break Logic:**
- `rt_debug_should_break()` - Checks breakpoints and step mode
  - Breakpoint hit detection
  - StepIn: Break on every statement
  - StepOver: Break at same or lower depth
  - StepOut: Break at lower depth

**Stack Frames:**
- `rt_debug_push_frame(func_name, file, line, column)`
- `rt_debug_pop_frame()`
- `rt_debug_stack_depth()`
- `rt_debug_stack_trace()` - Returns JSON format

**Variables:**
- `rt_debug_set_local(name, value)` / `rt_debug_set_global(name, value)`
- `rt_debug_locals()` / `rt_debug_globals()` - Returns JSON arrays
- `rt_debug_clear_locals()` / `rt_debug_clear_globals()`

### ✅ Phase 2.2: Simple FFI Declarations (Complete)

**File:** `src/ffi/debug.spl` (Updated)

Added declarations matching Rust implementation:
- All 30+ extern fn declarations
- Wrapper functions with type conversions
- Boolean conversions (i64 ↔ bool)
- String handling (text with .ptr() and .len())

**Example:**
```simple
extern fn rt_debug_is_active() -> i64
extern fn rt_debug_set_active(active: i64)

fn debug_is_active() -> bool:
    rt_debug_is_active() != 0

fn debug_set_active(active: bool):
    rt_debug_set_active(if active: 1 else: 0)
```

### ✅ Phase 2.3: Interpreter Hooks (Started)

**File:** `src/compiler/backend.spl` (Modified)

Added debug hooks to eval_expr():
```simple
fn eval_expr(expr: HirExpr, ctx: EvalContext) -> Result<Value, BackendError>:
    # Debug hooks for DAP integration
    if debug_is_active():
        # Track current location
        val span = expr.span
        debug_set_current_location(span.file, span.line as i64, span.column as i64)

        # Check if we should pause execution
        if debug_should_break():
            debug_wait_for_continue()

    match expr.kind:
        # ... expression evaluation ...
```

**Imports Added:**
```simple
use ffi.debug (debug_is_active, debug_set_current_location, debug_should_break, debug_wait_for_continue)
```

## Files Created/Modified

| File | Status | Lines | Description |
|------|--------|-------|-------------|
| `build/src/bootstrap_ffi_debug.rs` | ✅ Created | 444 | Rust debug FFI implementation |
| `build/src/bootstrap_ffi.rs` | ✅ Modified | +5 | Import debug module |
| `src/ffi/debug.spl` | ✅ Modified | +80 | FFI declarations |
| `src/compiler/backend.spl` | ✅ Modified | +13 | Debug hooks in eval_expr |

## Technical Design

### Debug Flow

1. **Setup:**
   - User enables debugging: `debug_set_active(true)`
   - User sets breakpoints: `debug_add_breakpoint("file.spl", 10, 1)`
   - User sets step mode: `debug_set_step_mode(StepOver)`

2. **Execution Loop:**
   ```
   For each expression:
     → Track location (file:line:col)
     → Check should_break()
       → Has breakpoint?
       → Step mode match?
     → If break: wait_for_continue()
     → Evaluate expression
   ```

3. **Breakpoint Hit:**
   - Interpreter: `should_break()` returns true
   - Interpreter: Calls `wait_for_continue()` (blocks)
   - User: Inspects variables via `debug_locals()`
   - User: Calls `debug_continue()`
   - Interpreter: Resumes execution

### Step Mode Logic

**StepIn (mode=2):** Break on every statement
```rust
match step_mode {
    StepMode::StepIn => 1,  // Always break
    // ...
}
```

**StepOver (mode=1):** Break when depth ≤ start_depth
```rust
StepMode::StepOver => {
    if stack_depth <= step_start_depth { 1 } else { 0 }
}
```

**StepOut (mode=3):** Break when depth < start_depth
```rust
StepMode::StepOut => {
    if stack_depth < step_start_depth { 1 } else { 0 }
}
```

## Known Issues

### 🔴 Build Error (Blocking)
**Error:** `method 'split' not found on type 'enum'`
**Location:** Unknown (no line number provided)
**Impact:** Cannot rebuild runtime with new FFI functions
**Status:** Needs investigation

**Workaround:** Continue implementing remaining phases while investigating build issue separately.

### ⚠️ Incomplete Features

1. **Variable Capture:** Not yet implemented in interpreter hooks
   - TODO: `debug_update_variables(ctx.env)` in eval_expr
   - Need to traverse environment and call `debug_set_local()` / `debug_set_global()`

2. **Stack Frame Tracking:** Not yet implemented
   - Need to call `debug_push_frame()` on function entry
   - Need to call `debug_pop_frame()` on function exit

3. **Source Location:** Depends on Span having file/line/column fields
   - May need parser changes to capture source locations

## Next Steps

### Immediate (Phase 2.3 completion)
1. ⏳ Fix build error to enable runtime rebuild
2. ⏳ Implement variable capture in eval_expr
3. ⏳ Add stack frame push/pop around function calls
4. ⏳ Test basic breakpoint functionality

### Phase 2.4: DAP Server Integration (Days 8-10)
- Replace mock data in `src/app/dap/server.spl`
- Implement real stack trace from `debug_stack_trace()`
- Implement real variables from `debug_locals()`
- Wire step commands to debug FFI

### Phase 2.5: Step Mode Implementation (Days 11-12)
- Implement step handlers (next, stepIn, stepOut)
- Test step modes with VS Code

### Phase 2.6: Testing & Integration (Days 13-16)
- Integration testing with VS Code
- Add source location metadata to parser
- Create `.vscode/launch.json`
- End-to-end debugging workflow

## Test Plan

### Unit Tests (After build fixed)
```simple
# Test 1: Basic state
debug_set_active(true)
assert(debug_is_active())

# Test 2: Breakpoints
debug_add_breakpoint("test.spl", 10, 1)
assert(debug_has_breakpoint("test.spl", 10))

# Test 3: Location tracking
debug_set_current_location("main.spl", 42, 5)
assert(debug_current_file() == "main.spl")
assert(debug_current_line() == 42)

# Test 4: Stack depth
debug_push_frame("test_func", "test.spl", 15, 0)
assert(debug_stack_depth() == 1)
debug_pop_frame()
assert(debug_stack_depth() == 0)
```

### Integration Tests (Phase 2.6)
- Set breakpoint in VS Code
- Run program with F5
- Verify breakpoint hits
- Inspect variables
- Step over/in/out
- Continue execution

## Performance Considerations

- ✅ **Polling overhead:** 10ms sleep in `wait_for_continue()` - acceptable for debugging
- ✅ **Thread-local storage:** Zero cost when debug inactive
- ✅ **Lock contention:** Single mutex, minimal critical sections
- ⚠️ **Every expression check:** `if debug_is_active()` on every eval_expr call
  - Cost: ~1 atomic load per expression
  - Acceptable for debugging, zero cost in production (debug inactive)

## Conclusion

Phase 2.1 (Rust Debug Infrastructure) is **complete** with 30+ FFI functions implemented. Phase 2.2 (FFI Declarations) is **complete** with all Simple wrappers added. Phase 2.3 (Interpreter Hooks) is **started** with basic location tracking and break checks.

**Blocker:** Build error prevents testing new FFI functions. Need to resolve `.split()` type error before proceeding with full integration.

**Ready for:** Completing Phase 2.3 (variable capture + stack tracking) once build is fixed.
