# engine2d native blend row/span diverges from scalar reference on varied pixel patterns

- **Date:** 2026-08-15
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Area:** src/runtime/runtime_simd_dispatch.c blend kernels vs src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl `_scalar_blend_row`
- **Severity:** correctness — violates the module's stated bit-identical contract

## Resolution (2026-08-15)

**The filing hypothesis was inverted: the native kernels were correct; the
scalar *reference* was mis-executing.** Both `engine2d_blend_pixel`
(src/runtime/runtime_simd_dispatch.c:1160) and `blend_pixel`
(src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs:156) already
implement the exact premultiplied-composite + divide-by-`out_a` formula of
`_scalar_blend_row`, including the `sa==255`/`sa==0` fast paths and da<255
unpremultiply — no truncating opaque-dst `/255` formula existed in the tree.

The real defect: `_scalar_blend_row`'s `dst` param is typed `any`, and in the
seed's `bin/simple run` MIR lane a bit-op on an any-typed array element
returns its result UNBOXED while consumers decode it as boxed (int tagging is
`v << 3`), so `da = (d >> 24) & 0xFF` came back as `f64::from_bits(80)`-style
garbage and `dst_weight`/`out_a` were wrong on any pixel taking the
translucent-blend branch (sa in 1..254) — hence exactly the varied-pattern
pixels diverging while the sa==255/sa==0 canonical-alpha spec inputs stayed
green. Root cause filed separately:
`doc/08_tracking/bug/seed_mir_any_binop_result_unboxed_2026-08-15.md`.

**Fix:** pin the element to a typed lane in the scalar reference —
`val d = dst[idx] as u32` (simd_kernels.spl `_scalar_blend_row`). No C or
Rust kernel change and no seed rebuild were needed.

**Evidence (2026-08-15, x86_64 AVX2 host, seed `bin/simple run`):**
- Per-pixel probe (640-px varied translucent src+dst,
  `engine2d_simd_blend_row_u32` vs `_scalar_blend_row`): 437/640 diffs before
  the cast, **0/640 after**.
- `test/perf/graphics_2d/bench_span_kernels.spl`: `SIMPLE_2D_SIMD=off` and
  `=auto` now both print `SPAN_BENCH_DONE checksum=316643543` (previously
  948743592 vs 316643543).
- New parity test "iterated const-src blends over translucent dst stay
  bit-identical to scalar" added to
  `test/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.spl`
  (18/18 pass). **Scope caveat (review 2026-08-15):** `bin/simple test` runs
  the interpreter lane, which was never affected — this spec guards formula
  parity, NOT the MIR-lane defect; it would have been green before the fix.
  The non-vacuous regression evidence is the run-lane bench checksum
  comparison above — now gated by
  `scripts/check/check-engine2d-runlane-blend-parity.shs` (off vs auto,
  fail-closed, verified PASS at 316643543); the root-cause fix
  (`seed_mir_any_binop_result_unboxed_2026-08-15.md`) must carry a run-lane
  probe. Note also: the C blend has vector paths only for SSE2/AVX2; NEON and
  RVV use the same scalar `engine2d_blend_pixel` loop, so "native kernels
  correct" is proven on AVX2 and structurally safe (same formula, no separate
  kernel) elsewhere. `simd_kernels_branch_coverage_spec.spl` 26/26,
  `engine2d_vulkan_image_compare_spec.spl` 2/2, `simd_kernels_spec.spl`
  50/51 (the 1 red is the pre-existing "cross-mode return-array span bridge"
  source-shape test from another session's backend_software.spl work, tracked
  outside this bug).

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
