# `Vec4f` f32 SIMD externs receive a boxed `Float32` instead of a raw `f32`

**Date:** 2026-07-20
**Component:** interpreter value-passing for `extern fn rt_simd_mul_f32x4`
(and likely sibling `rt_simd_{add,sub,div,fma}_f32x4`) in
`src/lib/nogc_sync_mut/simd.spl`, reached via
`src/lib/nogc_async_mut/linalg/simd_ops.spl::simd_dot4_f32_values`.
**Severity:** Medium — any caller building a `Vec4f` from a `std.ndarray`
`Float32` wrapper's `.value` field and passing it into an `rt_simd_*_f32x4`
extern crashes at runtime; f64 SIMD paths (`Vec4d`, if the analogous
wrapper is used) were not checked but should be audited for the same class.

## Symptom

`test/perf/scilib_simd_ops_perf_spec.spl`, example
`"records public SIMD-backed operation timings"`, fails at the
`simd_f32_dot_avg_ns` step (after the f64 dot/axpy steps already ran clean)
with:

```
runtime: rt_simd_mul_f32x4: field x must be a float, got Float32(1.0)
```

i.e. the `x` field of the `Vec4f` struct handed to the
`rt_simd_mul_f32x4` extern contains a boxed `Float32(value: f32)` struct
instance (from `std.ndarray`, `struct Float32: value: f32` with a
`static fn new(value: f32) -> Float32`) instead of the raw `f32` scalar
`Vec4f.x: f32` declares.

## Minimal repro

```simple
use std.spec
use std.ndarray.*
use std.linalg.*

describe "simd f32 dot repro":
    it "reproduces the boxed-Float32 crash":
        val left = vector_from_f32([Float32.new(1.0f32), Float32.new(2.0f32), Float32.new(3.0f32), Float32.new(4.0f32)])
        val right = vector_from_f32([Float32.new(4.0f32), Float32.new(3.0f32), Float32.new(2.0f32), Float32.new(1.0f32)])
        val result = dot_f32(left, right).unwrap()
        expect(result.value).to_equal(20.0f32)
```

Run: `bin/simple test <this file>` on the deployed binary
`bin/release/x86_64-unknown-linux-gnu/simple`.

## Root-cause hypothesis

`simd_dot4_f32_values` (`simd_ops.spl:123-138`) builds:

```simple
val left_vec = Vec4f(
    x: left[0].value,
    y: left[1].value,
    z: left[2].value,
    w: left[3].value
)
```

where `left: [Float32]` (the `std.ndarray` struct wrapper) and
`left[0].value` is field-accessed to obtain the raw `f32` before it is
placed into `Vec4f.x: f32`. Despite the source correctly reading
`.value` before assigning into a field explicitly typed `f32`, the value
that reaches the extern boundary (`rt_simd_mul_f32x4(a: Vec4f, b: Vec4f)`
via `simd_mul_f32x4` at `simd.spl:299-301`, a one-line passthrough) is
still the boxed `Float32` wrapper, not the unboxed scalar. This is the
same general class as the previously-fixed f64/enum heap-box interp/JIT
landmine (see MEMORY "Tag-box f64-enum fix", landed `aa7ae5506c6` /
`f33dc52320f`) — a scalar wrapped in a one-field struct fails to fully
unbox when threaded through nested struct-field construction into an
`extern fn` SFFI call — but this specific `f32`-into-`Vec4f`-field path
was not covered by that fix and reproduces independently on the currently
deployed binary. Not traced further into
`interpreter_extern/simd.rs`/`runtime/src/value/simd_*.rs` — that's the
next step for whoever picks this up.

## Notes

- Not attempted as a live fix here — this is interpreter/SFFI
  value-representation code (`.rs`), out of scope for a spec-triage sweep
  and requires a binary rebuild to verify any fix.
- Affected spec: `test/perf/scilib_simd_ops_perf_spec.spl`. It had a second,
  independent stale-API issue that was fixed and kept (not reverted): every
  `Float32.new(N.0)` call passed a bare literal (defaults to `f64`) to a
  `value: f32` static-method parameter, which the semantic checker rejects
  as "unknown static method new on class Float32" instead of a type-mismatch
  diagnostic — fixed by adding the required `f32` literal suffix
  (`Float32.new(N.0f32)`, 10 call sites). That fix is landed in the spec file
  as-is; it unblocked compilation and correctly exposed the real defect
  documented here. The spec is left RED (not weakened) against this
  remaining runtime bug — it is not in the triage pass's FIXED list because
  it does not go green.
