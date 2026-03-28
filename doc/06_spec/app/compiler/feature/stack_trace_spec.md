# stack_trace_spec

**Category:** System/DAP | **Status:** Passing

_Source: `test/feature/dap/stack_trace_spec.spl`_

---

## Features Tested

- Pushing stack frames
- Popping stack frames
- Stack depth tracking
- Stack trace formatting
- Multiple frames in trace
- Frame information accuracy

## Stack Frame Format

Each frame in the trace includes:
- Function name
- File path
- Line number
- Column number

Format: "file:line:column:function_name"

## Implementation

Uses FFI functions:
- debug_push_frame(func, file, line, column)
- debug_pop_frame()
- debug_stack_depth()
- debug_stack_trace()

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 23 |

## Test Structure

### Stack Frame Management
_Tests for stack frame push/pop operations._

### Pushing frames
_Test adding frames to call stack._

- ✅ pushes a single frame
- ✅ pushes multiple frames
- ✅ tracks frame information
### Popping frames
_Test removing frames from call stack._

- ✅ pops a single frame
- ✅ pops frames in LIFO order
- ✅ handles popping from empty stack
### Stack depth tracking
_Test accurate depth counting._

- ✅ starts at zero depth
- ✅ increments on push
- ✅ decrements on pop
### Stack trace generation
_Test stack trace string generation._

- ✅ generates trace for single frame
- ✅ generates trace for multiple frames
- ✅ includes file paths in trace
- ✅ includes line numbers in trace
- ✅ returns empty trace for empty stack
### Recursive call tracking
_Test tracking recursive function calls._

- ✅ tracks recursive calls
- ✅ maintains separate frame instances
### Edge cases
_Test boundary conditions and special cases._

- ✅ handles frames with zero line/column
- ✅ handles frames with large line numbers
- ✅ handles empty function names
- ✅ handles empty file paths
- ✅ handles special characters in names
### Performance
_Test performance with many frames._

- ✅ handles deep call stacks
- ✅ efficiently pops many frames

