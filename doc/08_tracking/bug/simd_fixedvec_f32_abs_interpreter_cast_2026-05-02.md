# Bug: FixedVec<f32>.abs() — "cannot cast i64 to T" in interpreter mode

**Date:** 2026-05-02
**Severity:** Medium — blocks CT-06 abs test in cross-target equivalence harness
**Affects:** Interpreter mode only (compiled mode not verified)
**File:** `src/lib/nogc_sync_mut/simd/fixed.spl` line 181

## Symptom

Calling `.abs()` on a `FixedVec<f32>` produces:

```
semantic: type mismatch: cannot cast i64 to T
```

at runtime in interpreter mode.

## Root Cause

`FixedVec.abs()` compares each element against `0 as T`:

```spl
if v < 0 as T:
```

The integer literal `0` is typed as `i64` by the interpreter. The `as T` cast to
a generic `T` (here instantiated as `f32`) is not resolving in interpreter mode —
the interpreter lacks the generic-numeric-cast path that would convert `i64 → f32`
through the `T` parameter.

## Reproduction

```spl
use std.simd.aliases.{vec4f_from_array}
val vc = vec4f_from_array([0.25, 1.0, -3.5, 2.0])
val result = vc.abs()   # fails: "cannot cast i64 to T"
```

## Proposed Fix

Replace `0 as T` with a typed zero via the existing `fixedvec_zero()` constructor
or compare against a lane extracted from a zero vector, so no integer literal cast
through T is required.  Alternatively, use `T::zero()` once that trait method lands.

## Impact

- `test/unit/lib/simd/cross_target_simd_spec.spl` CT-06 is using `reduce_min`
  as a stand-in until this is fixed.  When fixed, CT-06 should be replaced with
  a proper abs test covering `vc=[0.25, 1.0, -3.5, 2.0]` → `[0.25, 1.0, 3.5, 2.0]`.

## Related

- `src/lib/nogc_sync_mut/simd/fixed.spl` §abs (line 175–186)
- `src/lib/nogc_sync_mut/simd/fixed.spl` §recip (line 188–195) — same `1 as T` pattern,
  may have same bug
