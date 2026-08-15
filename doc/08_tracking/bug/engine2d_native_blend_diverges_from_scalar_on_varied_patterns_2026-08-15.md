# engine2d native blend row/span diverges from scalar reference on varied pixel patterns

- **Date:** 2026-08-15
- **Status:** OPEN
- **Area:** src/runtime/runtime_simd_dispatch.c blend kernels vs src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl `_scalar_blend_row`
- **Severity:** correctness — violates the module's stated bit-identical contract

## Symptom

`engine2d_simd_blend_row_u32` and `rt_engine2d_simd_blend_span_u32` agree with
each other but diverge from `_scalar_blend_row` on **350 of 640 pixels** of the
span-bench's varied pixel pattern. Measured 2026-08-15 (x86_64 AVX2 host):

- `bin/simple run test/perf/graphics_2d/bench_span_kernels.spl` checksum under
  `SIMPLE_2D_SIMD=auto` (native rows): **316643543**
- Same bench under `SIMPLE_2D_SIMD=off` (pure scalar): **948743592**

So off vs auto are NOT byte-identical on arbitrary patterns, contradicting the
"Output is bit-identical to the scalar reference" comments in
`simd_kernels.spl` (Native-SIMD routing gate section) and the C kernel header.

## Why existing parity specs stayed green

`simd_kernels_config_matrix_spec.spl` and `simd_kernels_spec.spl` blend tests
use uniform/canonical-alpha sources (e.g. constant `0x804488CC`), where both
paths agree. The divergence appears on varied per-pixel alpha/color patterns —
likely a rounding/unpremultiply mismatch: `_scalar_blend_row` composites in
premultiplied space and divides by `out_a` (simd_kernels.spl:439-444), while
the C kernel reportedly uses a truncating `/255` floor formula. The two are not
the same function on non-opaque destinations.

## Wanted

1. Decide the canonical formula (scalar `_scalar_blend_row` is the spec per
   module docstring) and make the C/Rust kernels match it exactly, OR update
   the contract + scalar reference if the C formula is intended.
2. Add a varied-pattern blend parity test (per-pixel pseudorandom src/dst incl.
   translucent dst) to `simd_kernels_config_matrix_spec.spl` so the gate can't
   stay green on canonical inputs only. It must run under both `off` and `auto`
   and require identical output.

## Repro

See "Attempt 2026-08-15" in
`engine2d_interpreter_span_kernel_marshalling_perf_gap_2026-08-14.md` for the
probe method (blend a varied 640-px pattern via `engine2d_simd_blend_row_u32`
and `_scalar_blend_row`, diff per pixel).

Verification blocked at filing time by the repo-wide bootstrap resource lock;
commands above not run since the revert — numbers are from the recorded probe.
