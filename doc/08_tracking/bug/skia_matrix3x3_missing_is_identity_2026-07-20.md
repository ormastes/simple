# Skia Matrix3x3 missing `is_identity()` method
**Status:** RESOLVED (2026-09-12, re-verified: bin/simple test test/unit/lib/skia/matrix_spec.spl -> 18 passed, 0 failed)

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

## Triage 2026-09-12
Rule B: ran `bin/simple test test/unit/lib/skia/matrix_spec.spl` on the deployed seed; the spec now passes in full (18/18), so this record no longer reproduces. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Re-check 2026-09-12

- Status: CLOSED (2026-09-12) — not reproducible on `3d120a6f9ab5`
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 `3d120a6f9ab5`

`Matrix3x3` moved to `src/lib/common/drawing/vector.spl` (`src/lib/skia/entity/matrix.spl`
is now a re-export shim) and that class carries `fn is_identity(self) -> bool`
at `vector.spl:223`, implemented with an epsilon comparison rather than the
exact `== 1.0` sketch in this record, precisely because `rotate_degrees(0.0)`
and `scale(1.0, 1.0)` only reach the identity up to f64 rounding.

```
$ bin/simple test test/01_unit/lib/skia/matrix_is_identity_spec.spl --no-session-daemon
SPEC FILE VERDICT: test/01_unit/lib/skia/matrix_is_identity_spec.spl outcome=OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0

$ bin/simple test test/unit/lib/skia/matrix_spec.spl --no-session-daemon
SPEC FILE VERDICT: test/unit/lib/skia/matrix_spec.spl outcome=OK declared>=18 executed=18 passed=18 failed=0 skipped=0 dropped=0
```

The 18/18 on the exact spec file this record names (13/18 when filed, with all
five `is_identity` examples red) is the direct refutation.
