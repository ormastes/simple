# Skia Matrix3x3 missing `is_identity()` method

## Closed 2026-11-25 — `is_identity()` exists and covers every element; verified by inspection

- **measured (source)** `Matrix3x3.is_identity()` is defined at
  `src/lib/common/drawing/vector.spl:224` (the class moved there from
  `src/lib/skia/entity/matrix.spl` on 2026-08-09; `matrix.spl` now re-exports
  it). The implementation compares all nine elements against the identity with
  a small f64 tolerance, so `translate`/`scale(1,1)`-via-rounding/`rotate(0)`
  cases the spec exercises are all handled. This is exactly the method the
  2026-07-20 entry reported missing.
- **measured (source)** a dedicated regression spec exists:
  `test/01_unit/lib/skia/matrix_is_identity_spec.spl` ("reproducing spec" +
  "detection spec" generalising the class), alongside the original
  `test/01_unit/lib/skia/matrix_spec.spl`.
- **limit** the spec could not be executed in this lane:
  `SIMPLE_LIB=src bin/simple.exe test test/01_unit/lib/skia/matrix_spec.spl
  --mode=interpreter` fails before any example runs with
  `unknown decorator '@representation_boundary'` inside the pinned rc.1 seed's
  own test-runner closure (`src/app/test_runner_new/test_runner_client.spl`) —
  the known release/1.0.0 HEAD source/binary inconsistency, unrelated to this
  bug. Verification is therefore by code inspection plus the presence of the
  dedicated regression spec, not a fresh green run.
- Status: **CLOSED (fixed)**.

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-07-20
**Category:** GENUINE-BUG (missing method, not a rename)
**Spec:** `test/unit/lib/skia/matrix_spec.spl` (13/18 passing)
**Command:** `SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple test test/unit/lib/skia/matrix_spec.spl --no-session-daemon`

## Symptom

Exactly 5 of 18 examples fail: `is_identity returns true for identity`,
`translate is not identity`, `scale 1,1 is identity`, `rotate 0 degrees is
identity`, `identity times identity is identity` — i.e. every example that
calls `m.is_identity()`. The other 13 examples (constructors, translate,
scale, rotate, multiply, and the `tx()/ty()/scale_x()/scale_y()` accessor
decomposition tests) all pass, confirming SSpec evaluates examples
independently and this is the *only* gap.

## Root cause

`src/lib/skia/entity/matrix.spl`'s `Matrix3x3` class defines `identity()`,
`translate()`, `scale()`, `rotate_degrees()`, `mul()`, `tx()`, `ty()`,
`scale_x()`, `scale_y()` — but no `is_identity()` method exists anywhere on
the class (confirmed by reading the full ~128-line source; no equivalently
named method under another spelling either).

## Suggested fix (not applied — new method, out of scope for a rename-only pass)

```
fn is_identity() -> bool:
    self.m00 == 1.0 and self.m01 == 0.0 and self.m02 == 0.0 and
    self.m10 == 0.0 and self.m11 == 1.0 and self.m12 == 0.0 and
    self.m20 == 0.0 and self.m21 == 0.0 and self.m22 == 1.0
```

Trivial to add, but per the cluster-fix guide's hard prohibition
("No src/** edits unless the fix is unambiguously a one-line import/rename"),
adding a brand-new method is out of scope for this pass even though it's
short — filed here instead.

