# Bug: FixedVec<f32>.abs() — "cannot cast i64 to T" in interpreter mode

**Date:** 2026-05-02
**Status:** RESOLVED — 2026-05-19
**Resolution:** Fixed via `val zero = v - v` (self-subtraction produces typed zero, no `i64` cast).
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

## Resolution Details

`abs()` at `fixed.spl:175-187` now uses:
```spl
val zero = v - v   # typed zero via self-subtraction — no i64 literal cast needed
if v < zero:
```
CT-06 in `test/01_unit/lib/simd/cross_target_simd_spec.spl` tests a real `.abs()` call
(not the `reduce_min` stand-in mentioned in the original report) and passes:
```
FixedVec<f32,4> cross-target equivalence — abs
  ✓ CT-06: abs matches scalar reference for all four lanes
```
All 9 cross-target SIMD tests pass (201ms).

## Impact (original, now resolved)

- `test/01_unit/lib/simd/cross_target_simd_spec.spl` CT-06 was using `reduce_min`
  as a stand-in; it has since been updated to the real abs test and passes.

## Related / Follow-up

- `src/lib/nogc_sync_mut/simd/fixed.spl` §abs (line 175–187) — **fixed**
- `src/lib/nogc_sync_mut/simd/fixed.spl` §recip (line 189–196) — still uses `1 as T / self.elements[i]`,
  same cast pattern; follow-up bug if recip is called on `FixedVec<f32>` in interpreter mode
- `src/lib/nogc_sync_mut/simd/fixed.spl` §recip_sqrt (line 207–213) — same `1 as T` pattern,
  follow-up
