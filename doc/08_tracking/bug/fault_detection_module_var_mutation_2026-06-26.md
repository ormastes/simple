# Bug: fault_detection_enhanced_spec — module-level var mutation inside fn not visible in test runner

**Date:** 2026-06-26
**Spec:** test/01_unit/lib/common/fault_detection_enhanced_spec.spl
**Status:** CLOSED (2026-09-12) — not reproducible on seed sha256 `3d120a6f`

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

## Triage 2026-09-12
Rule B: re-ran `bin/simple test test/01_unit/lib/common/fault_detection_enhanced_spec.spl` on the deployed seed; it still FAILs, matching the recorded defect. Status word left as-is. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Re-check 2026-09-12

Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust bootstrap seed,
`Simple Language v1.0.0-rc.1`), sha256 prefix `3d120a6f`.

### The original repro still exists, intact, and passes

The two live test trees had drifted apart, and that matters here: the
`test/unit/` copy is still the **module-level `var` form** this record was
written against — `var _signal_detected = false` at module scope, `fn
set_signal(...)` mutating it, assertions reading it back after the call. That is
the exact shape the record says the interpreter got wrong.

```
SIMPLE_RUST_SEED_WARNING=0 timeout 420 bin/simple test \
  test/unit/lib/common/fault_detection_enhanced_spec.spl --no-session-daemon
SPEC FILE VERDICT: test/unit/lib/common/fault_detection_enhanced_spec.spl \
  outcome=OK declared>=19 executed=19 passed=19 failed=0 skipped=0 dropped=0
```

All 19 pass, including the six the record names (`set marks active` x3,
`stores signal number` expecting 6, `stores signal name` expecting "SIGABRT",
`stores used and limit` expecting 512/256). Writes to module-level `var` made
inside a function body **are** visible to the module scope on this binary. No
compiler change was needed and none was made.

### A different defect was found in the other tree, and fixed

`test/01_unit/lib/common/fault_detection_enhanced_spec.spl` was structurally
corrupt — the product of a half-finished conversion from the module-var form to
a `FaultDetector` class. Two files had been spliced: a `fn clear_all():` whose
body was module-level assignments ran straight into a `me clear_all():` whose
body used `self.`, and the `class FaultDetector:` declaration line and its
fields were missing entirely. `FaultDetector` existed nowhere in the repository,
so every one of the 19 examples aborted with
`semantic: variable FaultDetector not found` — a 19/19 red that had nothing to
do with this bug.

Repaired by restoring the class the describe block was written against (11
fields with defaults, `static fn new()`, the five mutators, `clear_all`, and the
priority-ordering `check()`), which is now 19/19 green. The two trees stay
divergent by design — one exercises the module-var form, the other the class
form — so the baselined divergence row at
`scripts/check/test_tree_divergence_baseline.txt` remains valid.
