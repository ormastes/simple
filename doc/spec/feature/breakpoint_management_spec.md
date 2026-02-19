# breakpoint_management_spec

**Category:** System/DAP | **Status:** Passing

_Source: `test/feature/dap/breakpoint_management_spec.spl`_

---

## Features Tested

- Setting breakpoints via FFI
- Removing breakpoints
- Checking breakpoint existence
- Breakpoint hit detection
- Multiple breakpoints in same file
- Breakpoints across multiple files

## Implementation

Uses the FFI debug functions from src/lib/ffi/debug.spl:
- debug_add_breakpoint(file, line, id)
- debug_remove_breakpoint(file, line)
- debug_has_breakpoint(file, line)
- debug_should_break()

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 17 |

## Test Structure

### Breakpoint Management
_Tests for adding, removing, and checking breakpoints._

### Adding breakpoints
_Test breakpoint creation._

- ✅ adds a single breakpoint
- ✅ adds multiple breakpoints in same file
- ✅ adds breakpoints in different files
- ✅ allows duplicate breakpoints with different IDs
### Removing breakpoints
_Test breakpoint removal._

- ✅ removes a breakpoint
- ✅ removes specific breakpoint from multiple
- ✅ handles removing non-existent breakpoint
### Checking breakpoint existence
_Test breakpoint queries._

- ✅ returns false for non-existent breakpoint
- ✅ checks breakpoint in correct file only
- ✅ checks breakpoint at correct line only
### Breakpoint hit detection
_Test whether execution should break at current location._

- ✅ should break when at breakpoint location
- ✅ should not break when not at breakpoint
- ✅ should not break when debug inactive
### Edge cases
_Test edge cases and boundary conditions._

- ✅ handles line number 0
- ✅ handles large line numbers
- ✅ handles empty file path
- ✅ handles special characters in file path

