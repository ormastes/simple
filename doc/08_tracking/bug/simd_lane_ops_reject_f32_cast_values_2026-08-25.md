# `std.simd` lane ops reject values produced by `as f32` (2026-08-25)
## Status: FIXED (source fix `06c37c33347`, 2026-11-06; pinned by Rust tests 2026-11-06) — see "Resolution" below

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** FIXED — duplicate of `simd_f32x4_vec_field_boxed_float32_not_unwrapped_2026-07-20.md`. **Binary:** 08-23 seed (`/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple`).

## Symptom
Building a `Vec4f` from values that came through an `as f32` cast and calling a lane op fails:
```
rt_simd_mul_f32x4: field x must be a float, got Float32(1.0)
```
The runtime's argument check accepts the interpreter's `Float`/`Float64` value but not `Float32`,
so a genuinely-f32 value — the natural thing to feed a f32x4 op — is rejected while an f64 literal
is accepted. Found while porting the CUDA workbook's SIMD-vs-GPU module
(`examples/08_gpu/simple_cuda_example/70.gpu_optimization/71.MatMul_SIMD_vs_GPU`); worked around
there by keeping the values as plain floats.

## Impact
`std.simd` f32 lane ops (`simd_mul_f32x4` and siblings) are unusable on data typed `f32`, which is
exactly the data a GPU/SIMD comparison works with.

## Where to look
The `rt_simd_*_f32x4` argument extraction in the Rust runtime (field type check that names
`Float32`) — accept `Float32` alongside `Float`/`Float64`, or coerce.


## Resolution (2026-11-06)

Root cause: `require_f64_field` in
`src/compiler_rust/compiler/src/interpreter_extern/simd.rs` (~line 524), the
lane extractor behind `unpack_vec4f`/`unpack_vec8f`/`unpack_vec4d`, matched
`Value::Float` and `Value::Int` but not `Value::Float32`, so a lane holding an
`f32` value (`x as f32`, a `Float32.value` field) was rejected with
"field x must be a float, got Float32(1.0)". The "boxed Float32 struct"
reading in the original record was the `Debug` print of `Value::Float32`, not
a wrapper object.

The `Value::Float32(n) => Ok(*n as f64)` arm was first added in `45a0e1636ad`
(2026-08-23), was lost again before `release/1.0.0`, and was re-added in
`06c37c33347` (2026-11-06). This lane added Rust regression tests so it
cannot silently regress a third time:
`interpreter_extern::simd::f32_lane_value_tests::f32x4_lane_ops_accept_float32_fields`
and `f32x8_lane_ops_accept_float32_fields` — FAILED with the arm removed
(`Runtime("rt_simd_mul_f32x4: field x must be a float, got Float32(1.0)")`,
`... rt_simd_fma_f32x8: field e0 ...`), ok with it.

Repro `test/fixtures/seed_interp/simd_f32x4_float32_repro.spl` (interpreter):
before (seed `bin/simple.exe`, 2026-10-05): `error: runtime:
rt_simd_mul_f32x4: field x must be a float, got Float32(1.0)`; after (seed
built from `work/seed-interp-correctness-20261106`): `simd_mul_f32x4 2.0 4.0`.
