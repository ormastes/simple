# TUI Feature - FFI Module Blocker

**Date**: 2025-12-27
**Status**: 🔴 **BLOCKED** - FFI module infrastructure required

## Issue Summary

Cannot complete TUI feature implementation because the `ffi` module referenced in all Simple files does not exist in the Simple standard library.

## Error

```
error: semantic: undefined variable: ffi
```

## Affected Files

All TUI library files that use FFI:
1. `simple/std_lib/src/repl/__init__.spl` - Line 4: `use ffi`
2. `simple/std_lib/src/ui/tui/backend/ratatui.spl` - Line 19: `use ffi`
3. `simple/app/repl/main.spl` - Imports modules that use FFI

## Root Cause

The Simple language files assume an `ffi` module exists that provides:
- `ffi.call("function_name", ...args)` - Call external FFI functions

But this module is not implemented in:
- `simple/std_lib/src/` - No ffi/ directory
- Runtime - No FFI module registration

## What Works ✅

**Syntax fixes completed**:
- ✅ Array allocation: `alloc[u8](size)` instead of `[T; N]`
- ✅ Enum definitions: `Key` instead of `Key = 0`
- ✅ Triple-quoted strings: Use `\n` concatenation
- ✅ Doc comments: `##` patterns work correctly

**Files parse correctly** (when FFI dependency removed):
- Type definitions work
- Const definitions work
- Enum definitions work
- Doc comments work

## What's Blocked ❌

Cannot test or run any FFI-dependent code:
- REPL execution bindings
- Ratatui backend bindings
- LineEditor widget
- REPL application

## Required Solution

### Option 1: Implement FFI Module (Recommended)

Create `simple/std_lib/src/ffi/__init__.spl`:
```simple
# FFI Module - Foreign Function Interface
# Provides access to external Rust functions

## Call an external FFI function
##
## Example:
##   let result = ffi.call("ratatui_terminal_new")
##   let result = ffi.call("some_function", arg1, arg2)
pub fn call(name: str, ...args) -> Any:
    # Implemented in Rust runtime
    # Maps to extern functions registered in Runtime
    extern_call(name, args)
```

**Implementation needed**:
1. Create FFI module in Simple stdlib
2. Implement `extern_call` in Rust runtime
3. Register FFI functions with runtime
4. Map Simple calls to Rust FFI bridges

### Option 2: Direct Extern Declarations

Allow declaring extern functions directly:
```simple
# In ratatui.spl
extern "C" fn ratatui_terminal_new() -> u64

pub fn terminal_new() -> TerminalHandle:
    return ratatui_terminal_new()
```

**Pros**: No FFI module needed
**Cons**: Verbose, requires many extern declarations

### Option 3: Mock FFI for Testing

Create a mock FFI module for testing:
```simple
# simple/std_lib/src/ffi/__init__.spl
pub fn call(name: str, ...args) -> Any:
    # Mock implementation
    return 0
```

**Pros**: Allows syntax testing
**Cons**: Doesn't actually call Rust FFI

## Current State

**Rust Infrastructure**: ✅ 100% Complete
- `src/runtime/src/value/ratatui_tui.rs` - Working FFI bridge
- `src/driver/src/repl_runner_ffi.rs` - Working REPL FFI
- All C-compatible FFI functions implemented
- All tests passing (4/4)

**Simple Syntax**: ✅ 95% Complete
- All syntax errors identified and fixed
- Array allocation corrected
- Enum definitions corrected
- String handling corrected

**FFI Integration**: ❌ 0% Complete
- No FFI module in stdlib
- No mechanism to call extern functions from Simple
- Blocker for all FFI-dependent features

## Impact

**TUI Feature**: Cannot be completed without FFI module
**REPL Application**: Cannot run without FFI module
**Other FFI Features**: All blocked (GPU, ML, Graphics, etc.)

## Recommendation

**Short-term**: Document TUI as "Infrastructure Complete, FFI Pending"
- Rust FFI bridges are done and tested
- Simple syntax is correct
- Architecture is validated
- Waiting on FFI module infrastructure

**Long-term**: Prioritize FFI module implementation
- Required for TUI, GPU, ML, and all external integrations
- Core infrastructure piece
- Enables entire category of features

## Workaround for Testing

Can test individual components without FFI:
```simple
# Test type definitions
pub type TerminalHandle = u64
pub enum EventType:
    Key
    Mouse
    Resize

# Test constants
pub const KEY_ENTER: u32 = 13
```

But cannot test functions that call FFI.

---

**Status**: ✅ Syntax complete, ❌ FFI module required
**Estimated FFI Module Implementation**: 8-12 hours (design + implement + test)
**Unblocks**: TUI, REPL, GPU, ML, Graphics, and all FFI-dependent features
