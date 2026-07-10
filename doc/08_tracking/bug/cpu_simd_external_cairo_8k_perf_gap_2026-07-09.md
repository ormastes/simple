# CPU-SIMD External Cairo 8K Perf Gap

- **Date:** 2026-07-09
- **Status:** open
- **Severity:** high
- **Area:** GUI Web 2D, CPU-SIMD, performance

## Summary

The retained full-size 8K GUI benchmark shows Simple Web CPU-SIMD is still
slower than the available external CPU drawing-library baseline on this host.
This is an optimization blocker, not a correctness blocker.

## Evidence

`doc/09_report/gui_perf_benchmark_2026-07-08.md` records:

- Simple Web CPU-SIMD: `1282.166 ms` p50 at `7680x4320`, 300dpi, no screen-size
  reduction, checksum `sum32:135445232233405312`.
- Node Canvas/Cairo: `80.201 ms` p50 at the same 8K size.
- `gui_perf_cpu_base_compare_target_met=no`.

Follow-up optimization on 2026-07-09 removed per-character glyph row-array
allocation from the CPU text path and re-ran the same retained 8K row:

- Simple Web CPU-SIMD: `938.678 ms` p50 at `7680x4320`, 300dpi, no screen-size
  reduction, checksum `sum32:135445232233405312`.
- Improvement versus the recorded 2026-07-08 row: `26.8%`.
- Remaining gap versus Node Canvas/Cairo: `11.7x` slower.
- Evidence report: `doc/09_report/cpu_simd_text_glyph_inline_perf_2026-07-09.md`.
- Current owner blocker:
  `doc/08_tracking/bug/browser_layout_large_simd_fill_facade_unsafe_2026-07-09.md`.

The current external CPU baseline refresh after the compare contract added
explicit quality and no-screen-reduction proof records:

- Simple Web CPU-SIMD: `767.872 ms` p50 at `7680x4320`, 300dpi, no screen-size
  reduction, checksum `sum32:135445232233405312`, pixel proof
  `nonzero_pixels:33177600`.
- Simple Web scalar software: `799.203 ms` p50 with the same checksum.
- Node Canvas/Cairo: `73.892 ms` p50 at the same 8K size.
- `gui_perf_cpu_base_compare_dpi_source=default`.
- `gui_perf_cpu_base_compare_schedule_order=cpu_simd_first`.
- `gui_perf_cpu_base_compare_physical_pixels=7680x4320`.
- `gui_perf_cpu_base_compare_screen_size_reduced=false`.
- `gui_perf_cpu_base_compare_simple_checksum=sum32:135445232233405312`.
- `gui_perf_cpu_base_compare_simple_pixel_proof=nonzero_pixels:33177600`.
- `gui_perf_cpu_base_compare_runtime_compute_target=cpu_simd`.
- `gui_perf_cpu_base_compare_render_readback_scope=software-render-loop`.
- `gui_perf_cpu_base_compare_fallback_used=false`.
- `gui_perf_cpu_base_compare_target_met=no`.
- Current evidence report:
  `doc/09_report/gui_perf_benchmark_2026-07-09_cpu_base.md`.
- Remaining gap versus Node Canvas/Cairo: `10.4x` slower.

`doc/09_report/cpu_simd_render_scale_contract_2026-07-08.md` separately proves
the CPU-SIMD path beats the in-repo scalar software path for the focused 4K/8K
contract, so the remaining gap is external drawing-library parity.

## Expected

Either Simple Web CPU-SIMD reaches the external CPU drawing-library baseline for
the retained 8K scene, or the report keeps this blocker open with the measured
ratio and the bottleneck owner.

## 2026-07-10 stale deployment correction

The retained `767.872 ms` Simple row does not measure the optimized
`rt_array_repeat` implementation currently checked into the repository.
`bin/simple` resolves to the shared self-hosted release binary built on
2026-07-03. Disassembly of that binary's `rt_array_repeat` shows one
`rt_array_push` call per element; it does not contain the current first-store
plus doubling-`memcpy` implementation.

A focused full-8K repeat probe on that deployed binary measured `762414us` for
33,177,600 elements, matching the framebuffer trace and proving that the
retained result is dominated by the stale push loop. The recorded `10.4x`
Cairo ratio remains valid for the deployed 2026-07-03 binary, but it is not
valid evidence for the current source implementation.

An isolated pure-Simple bootstrap was attempted with the current source. Stage
2 failed at the known bootstrap LLVM/`llc` lane, and the seed-driven Cranelift
Stage 4 remained CPU-bound for 18 minutes without producing an executable. The
attempt was stopped at the existing bounded bootstrap ceiling. Three focused
AOT probe variants also failed in the current LLVM undefined-SSA/Cranelift type
lowering lane, so no substitute fresh executable was accepted.

Do not introduce packed framebuffer storage or another SIMD facade based on
the stale timing. First produce a fresh self-hosted CLI, confirm its
`rt_array_repeat` no longer contains the per-element push loop, then run the
retained 4K/8K and external Cairo comparisons once.

### Focused current-runtime result

After repairing Stage 2 LLVM emission, a standalone native probe compiled with
the fresh bootstrap runtime allocated and filled 33,177,600 `u32` elements,
validated the array length and final 32-bit color, and exited zero in `0.21 s`
wall time at `260096 KiB` max RSS. Its disassembly calls `memcpy` from
`rt_array_repeat`; it does not call `rt_array_push`.

This is a 3.6x improvement over the `0.762 s` stale push-loop probe and proves
the checked-in bulk-fill runtime is materially faster. It is not a replacement
for the retained full-render comparison: the fresh Stage 4 CLI currently fails
its standard smoke because its link accepted unresolved stubs, so no fresh
4K/8K or Cairo row is claimed yet.

## Next Step

Do not repeat the viewport/DPI/fallback/color proof work. The retained evidence
already proves full 8K size, default 300dpi, configurable DPI override, checksum
and pixel proof, CPU-SIMD runtime target, no fallback, and alpha-quality parity.
The immediate blocker is fresh self-host deployment, not another framebuffer
representation. Rebuild the pure-Simple CLI, verify the deployed
`rt_array_repeat` machine code uses the current bulk-fill implementation, and
then re-run the external CPU drawing-library comparison. Revisit the owner
facade only if that fresh measurement still shows a material gap.
