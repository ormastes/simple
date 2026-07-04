# Bug: Module-level var mutations via function calls do not propagate in interpreter

**Date:** 2026-06-26
**Spec:** `test/01_unit/lib/common/fault_detection_enhanced_spec.spl`

## Symptoms (6 failures)

Tests that call a helper function to mutate a module-level `var` see the initial value
instead of the mutated value:

```
fn set_signal(num: i64, name: text):
    _signal_detected = true   # assigns module-level var
    _signal_number = num
    _signal_name = name

it "detects SIGABRT":
    set_signal(6, "SIGABRT")
    expect(_signal_detected).to_equal(true)  # fails — still false
```

Tests that mutate module-level vars DIRECTLY (without a helper function) work correctly.
Tests that only READ the initial value of vars pass.

## Root cause

The interpreter does not propagate module-level `var` mutations made inside called
functions back to the caller's module scope. Mutations made directly at the call site
(no function indirection) are visible.

## Affected tests

All tests invoking `set_signal()`, `set_memory()`, `set_interrupt()`, or similar
helper functions and then checking the mutated module-level vars. Approximately 6
of 19 tests fail.

## Fix needed

Interpreter: function calls that mutate module-level (global) variables must write
those mutations back to the module scope after the call returns.
