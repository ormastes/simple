# debug_state_spec

**Category:** System/DAP | **Status:** Passing

_Source: `test/feature/dap/debug_state_spec.spl`_

---

## Features Tested

- Debug mode activation/deactivation
- Pause and continue operations
- Current location tracking
- State persistence
- Zero overhead when inactive

## Implementation

Uses FFI functions:
- debug_is_active() / debug_set_active()
- debug_pause() / debug_continue() / debug_is_paused()
- debug_set_current_location() / debug_current_file() / debug_current_line()

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 30 |

## Test Structure

### Debug Activation
_Tests for enabling/disabling debug mode._

- ✅ starts inactive by default
- ✅ activates debug mode
- ✅ deactivates debug mode
- ✅ toggles debug mode
### Pause and Continue
_Tests for pausing and resuming execution._

### Pause operations
_Test pausing execution._

- ✅ starts not paused
- ✅ pauses execution
- ✅ can pause multiple times
### Continue operations
_Test resuming execution._

- ✅ continues from paused state
- ✅ can continue when not paused
### Pause/continue cycle
_Test repeated pause/continue operations._

- ✅ handles multiple pause/continue cycles
### Location Tracking
_Tests for tracking current execution location._

### Setting location
_Test updating current location._

- ✅ sets current file and line
- ✅ updates location multiple times
- ✅ tracks location through different files
### Getting location
_Test retrieving current location._

- ✅ returns current file
- ✅ returns current line
- ✅ tracks line changes in same file
### Edge cases
_Test boundary conditions for location tracking._

- ✅ handles line 0
- ✅ handles large line numbers
- ✅ handles empty file path
- ✅ handles paths with special characters
- ✅ handles absolute paths
- ✅ handles relative paths
### State Persistence
_Tests that debug state persists correctly._

- ✅ maintains state across operations
- ✅ preserves location when toggling debug
### Performance and Overhead
_Tests for minimal overhead when debug is off._

- ✅ has no overhead when inactive
- ✅ handles high frequency location updates
### Integration Scenarios
_Tests combining multiple debug features._

- ✅ tracks location while stepping
- ✅ maintains breakpoints while paused
- ✅ tracks location with active breakpoints
- ✅ handles full debug session lifecycle

