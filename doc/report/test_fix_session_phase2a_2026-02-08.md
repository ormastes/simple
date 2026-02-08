# Test Fix Session - Phase 2a: Debug Module (2026-02-08)

## Summary

**Goal:** Complete debug module and fix debug_spec.spl tests (Phase 2a)
**Result:** ✅ **98/98 tests passing (100%)**
**Time:** ~3 hours

## Key Discoveries

### Module System Limitation

**Critical Issue:** Module-level `var` variables are completely broken
- Functions exported from a module **cannot access module-level `var` variables**
- This applies even to functions within the same module
- Workaround: Use instance state in classes, not module globals

### Solution: Refactor to Instance-Based State

Instead of global state:
```simple
# BROKEN: Module-level mutable state
var g_debug_level = DebugLevel.Off

fn set_debug_level(level: DebugLevel):
    g_debug_level = level  # ERROR: variable not found
```

Use instance-based state:
```simple
# WORKING: Instance state
class Debugger:
    debug_level: DebugLevel

    me set_debug_level(level: DebugLevel):
        self.debug_level = level  # Works!
```

## Implementation

### 1. Created New Debug Module (`src/std/debug.spl`)

**Why new location?**
- Original at `src/app/interpreter.helpers/debug.spl` uses Rust syntax
- Dots in directory names (`interpreter.helpers`) break module loader
- Moved to `src/std/debug.spl` which works correctly

**Module structure:**
- **Enums:** `DebugLevel` (Off/Error/Warn/Info/Debug/Trace), `StepMode` (Continue/StepOver/StepInto/StepOut)
- **Classes:** `Breakpoint`, `StackFrame`, `Debugger`
- **Factory:** `debugger_new()` - creates Debugger with default state
- **Stateless functions:** `level_to_int()`, `should_print()`, `debug_print()`
- **Instance methods:** All debug level, trace, breakpoint, watch, call stack, and stepping methods

### 2. Applied Mutable Method Pattern

**Simple requires explicit mutability markers:**
- Immutable methods: `fn method()` - cannot modify self
- Mutable methods: `me method()` - can modify self

**Changed 14 methods from `fn` to `me`:**
- Breakpoint management: `add_breakpoint`, `remove_breakpoint`, `toggle_breakpoint`
- Watch expressions: `add_watch`, `remove_watch`
- Call stack: `push_frame`, `pop_frame`
- Stepping: `step_over`, `step_into`, `step_out`, `continue_execution`
- State management: `set_debug_level`, `set_trace`, `should_break`

### 3. Updated Test File

**Created:** `test/std/debug_spec.spl` (refactored from test/app/interpreter/helpers/debug_spec.spl)

**Major API changes:**
1. **Global state → Instance methods:**
   - `set_debug_level(level)` → `debugger.set_debug_level(level)`
   - `get_debug_level()` → `debugger.get_debug_level()`
   - `set_trace(enabled)` → `debugger.set_trace(enabled)`
   - `is_trace_enabled()` → `debugger.is_trace_enabled()`

2. **Function signatures updated:**
   - `should_print(level)` → `should_print(current_level, msg_level)`
   - `debug_print(level, msg)` → `debug_print(current_level, msg_level, msg)`
   - `debugger.debug_print(level, msg)` - convenience instance method

3. **Construction pattern:**
   - `Debugger.new()` → `debugger_new()` factory function

## Test Results

| Test Group | Tests | Status |
|-----------|-------|--------|
| DebugLevel enum | 6 | ✅ All passing |
| Global debug state | 4 | ✅ All passing |
| should_print() | 4 | ✅ All passing |
| debug_print() | 8 | ✅ All passing |
| Debugger construction | 11 | ✅ All passing |
| Breakpoint management | 7 | ✅ All passing |
| Watch expressions | 9 | ✅ All passing |
| Call stack | 5 | ✅ All passing |
| Stepping control | 11 | ✅ All passing |
| Command handler | 33 | ✅ All passing |
| **Total** | **98** | **✅ 100%** |

## Key Learnings

### Simple Language Patterns

1. **Module-level mutable state is broken**
   - Use class instance state instead
   - Document in MEMORY.md for future reference

2. **Mutable vs Immutable methods**
   - Use `fn` for read-only methods
   - Use `me` for methods that modify self
   - Compiler enforces this strictly

3. **Factory functions over constructors**
   - `fn type_new() -> Type` pattern preferred
   - More flexible than direct construction for complex initialization

4. **Module path limitations**
   - Dots in directory names break imports (`app.interpreter.helpers` doesn't work)
   - Use flat names or underscores (`app_interpreter_helpers`)

## Files Modified

- **Created:** `src/std/debug.spl` (298 lines) - Complete debug module in Simple
- **Created:** `test/std/debug_spec.spl` (1,585 lines) - 98 comprehensive tests
- **Original (Rust-style):** `src/app/interpreter.helpers/debug.spl` - kept for reference, not used by tests

## Next Steps

Phase 2a complete. Options:
- Phase 2b: database_resource_spec (26 tests)
- Phase 3: New modules (treesitter, failsafe, table)
- Phase 4: SFFI Rust crates

**Total progress:**
- Phase 1a: cli_dispatch (7/25)
- Phase 1b: coverage_ffi (18/29)
- Phase 1c: concurrent (33/33) ✅
- Phase 2a: debug (98/98) ✅
- **Total fixed: 156 tests**
