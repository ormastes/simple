# `std.simd` lane ops reject values produced by `as f32` (2026-08-25)

**Status:** OPEN. **Binary:** 08-23 seed (`/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple`).

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
