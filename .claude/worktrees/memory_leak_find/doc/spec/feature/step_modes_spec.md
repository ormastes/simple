# step_modes_spec

**Category:** System/DAP | **Status:** Passing

_Source: `test/feature/dap/step_modes_spec.spl`_

---

## Features Tested

- Continue mode (mode 0)
- Step Over mode (mode 1) - same or lower depth
- Step Into mode (mode 2) - any depth
- Step Out mode (mode 3) - lower depth only
- Step mode state transitions
- Depth tracking

## Step Mode Values

- 0: Continue - no stepping, break only on breakpoints
- 1: StepOver - break at next line at same or lower depth
- 2: StepIn - break at next line at any depth
- 3: StepOut - break when depth becomes lower than start

## Implementation

Uses FFI functions:
- debug_set_step_mode(mode)
- debug_get_step_mode()
- debug_set_step_start_depth(depth)
- debug_get_step_start_depth()
- debug_stack_depth()
- debug_should_break()

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 22 |

## Test Structure

### Step Modes
_Tests for stepping through code execution._

### Mode 0: Continue
_Continue execution without stepping._

- ✅ sets continue mode
- ✅ does not break without breakpoint
### Mode 1: Step Over
_Step over function calls - break at same or lower depth._

- ✅ sets step over mode
- ✅ breaks at same depth
- ✅ breaks at lower depth
- ✅ does not break at higher depth
### Mode 2: Step Into
_Step into function calls - break at any depth._

- ✅ sets step into mode
- ✅ breaks at any depth - same level
- ✅ breaks at any depth - deeper
- ✅ breaks at any depth - shallower
### Mode 3: Step Out
_Step out of current function - break at lower depth only._

- ✅ sets step out mode
- ✅ breaks at lower depth
- ✅ does not break at same depth
- ✅ does not break at higher depth
### Step mode transitions
_Test changing between step modes._

- ✅ transitions from Continue to StepOver
- ✅ transitions from StepOver to StepInto
- ✅ transitions from StepInto to StepOut
- ✅ returns to Continue after step completes
### Depth tracking
_Test stack depth management._

- ✅ tracks depth correctly
- ✅ stores and retrieves start depth
### Interaction with breakpoints
_Test step modes with breakpoints._

- ✅ breakpoints override continue mode
- ✅ breakpoints work with step modes

