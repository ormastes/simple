# Bug: fault_detection_enhanced_spec — module-level var mutation inside fn not visible in test runner

## Closed 2026-09-13 — module-level `var` writes from inside a `fn` now propagate
- **measured** (Windows Rust seed v1.0.0-rc.1, `bin/simple run`): a repro with module-level `var _flag/_num/_name` mutated inside `fn set_signal(6, "SIGABRT")` printed `flag=true`, `num=6`, `name=SIGABRT` after return — exactly the three values this entry reports as lost.
- **inferred**: the spec itself was not re-run; `bin/simple test` is broken on this Windows host (a trivial 1-assertion spec also reports a false `outer-bound-timeout budget_ms=930000`).

**Date:** 2026-06-26
**Spec:** test/01_unit/lib/common/fault_detection_enhanced_spec.spl
**Status:** CLOSED 2026-09-13 (see Closed section above)

## Symptom

6 tests fail with "expected false to equal true" / "expected 0 to equal N":
- `set marks active` (signal/memory/interrupt contexts)
- `stores signal number` — expects 6, gets 0
- `stores signal name` — expects "SIGABRT", gets ""
- `stores used and limit` — expects 512/256, gets 0

## Root Cause

The spec defines module-level `var` state and functions that mutate it:
```
var _signal_detected = false
fn set_signal(num: i64, name: text):
    _signal_detected = true   # mutation NOT visible after fn returns
    _signal_number = num
```

The interpreter does not propagate writes to module-level `var` made inside a function body back to the module scope (same-file). The spec comment says it was "designed to test in interpreter mode" — the assumption was that same-file module-level var mutation would work, but it does not.

## Impact

6 of 19 assertions fail. The spec intent is valid; the interpreter has a bug.

## Fix Required

In `src/compiler_rust/compiler/src/interpreter_eval.rs` (or equivalent): when a function body assigns to a name that exists in the enclosing module scope, the write must propagate back to module scope, not only to the function's local frame.
