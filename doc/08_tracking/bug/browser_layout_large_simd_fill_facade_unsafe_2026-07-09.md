# Browser Layout Large SIMD Fill Facade Unsafe

- **Date:** 2026-07-09
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** high
- **Area:** Simple Web layout, CPU-SIMD, runtime facade

## Summary

The retained 4K/8K Simple Web CPU-SIMD trace shows paint/fill bandwidth is the
remaining bottleneck, but the browser layout renderer cannot safely call the
current Engine2D SIMD fill externs directly for a full framebuffer.

## Evidence

`doc/09_report/cpu_simd_text_glyph_inline_perf_2026-07-09.md` records:

- Retained 8K trace: `paint_ms=776`, total `779724us`, checksum
  `sum32:135445232233405312`.
- Follow-up split trace: 4K `framebuffer_init_ms=188`, `paint_draw_ms=15`,
  `paint_ms=204`, checksum `sum32:32105444634193792`; 8K
  `framebuffer_init_ms=1503`, `paint_draw_ms=32`, `paint_ms=1535`, checksum
  `sum32:135445232233405312`. Both kept 300 DPI retina metadata, full physical
  size, and `screen_size_reduced=false`.
- `simd_fill_row` over a browser-layout framebuffer logged
  `unknown extern function: rt_engine2d_simd_fill_u32`, changed checksum, and
  slowed 4K trace to `878028us`.
- `engine2d_simd_fill_row_u32` over the full framebuffer segfaulted at 4K.
- Routing the 4K benchmark through
  `simple_web_layout_render_html_pixels_engine2d(..., "cpu_simd")` also fails
  before measurement with `unknown extern function: rt_engine2d_simd_fill_u32`,
  so the existing DrawIR fast path does not provide a safe browser-layout fill
  owner boundary yet.
- A safer owner-boundary experiment that routed `fb_rect`/`fb_rect_clip` row
  fills through `backend_software`'s existing `simd_fill_row` owner compiled and
  preserved checksum (`sum32:32105444634193792` at 4K,
  `sum32:135445232233405312` at 8K), but regressed 8K to `1543525us`, so it was
  rejected and reverted.
- Native `rt_array_repeat` now mitigates the framebuffer initialization path by
  filling the allocated backing words directly instead of pushing once per
  pixel; the Rust runtime mirror uses the same no-push shape. Clean sequential
  trace after the C native change: 4K `paint_ms=199`, total `202984us`; 8K
  `paint_ms=765`, total `768514us`, with unchanged checksums and no screen-size
  reduction. This does not expose a safe mutable Engine2D fill facade.
- A returned-array `rt_u32_alloc_filled(len, fill)` facade was tried as a
  smaller owner-boundary alternative, but direct native export segfaulted before
  writing SDN evidence. It was rejected and removed; browser layout remains on
  compiler-lowered `[base; width * height]`, backed by the optimized native
  `rt_array_repeat` path.

The existing row-returning facade is proven only for small evidence rows
(`count=64`) in `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`.
Framebuffer-scale browser layout fill needs a safe owner facade instead of
directly calling the Engine2D internals.

## Expected

Either:

- browser layout gets a safe, checksum-preserving framebuffer fill facade with
  retained 4K/8K evidence, or
- the renderer keeps using pure Simple framebuffer initialization and the
  external Cairo gap remains open.

## Next Step

Design the facade at the runtime/Engine2D owner boundary so native builds can
fill a browser-layout `[u32]` framebuffer without missing externs, returned-array
segfaults, checksum drift, or GPU backend behavior changes.

## 2026-07-09 containment

The canonical public row-fill facade was changed to stop exposing the unsafe
mutable extern path. `simd_fill_row` now uses the safe return-row SIMD ABI and
scatter writeback for row-sized fills, with interpreter and native spec coverage
in `test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl`.
The interpreter no-op registration for the mutable fill extern was removed too,
so accidental direct use fails closed instead of silently reporting fallback.

This is a correctness containment only. Browser layout full-frame 4K/8K fill
still needs a real mutable typed-array owner bridge before it can replace the
current compiler array-repeat framebuffer initialization/fill path.

## 2026-07-09 solid-only CPU-SIMD containment

`cpu_simd` browser readback now uses the existing Engine2D display-list path
only when layout classifies the frame as solid-only. That path reaches the
current `CpuBackend`/`SoftwareBackend` SIMD row-fill owner and is covered by
`web_renderer_cpu_simd_paint_spec.spl`.

The solid-only classifier was hardened to require an opaque background alpha, so
translucent `rgba(...)` and CSS opacity keep using the normal CPU mirror path.
The public Engine2D renderer also skips heuristic/probe routing for obvious
text pages requested as `cpu_simd`, avoiding a routing tax when no solid-fill
SIMD shortcut applies.

Full native scale-contract evidence after that routing containment shows the
Simple CPU-SIMD row beating the Simple scalar row at 4K and 8K while preserving
checksum parity, full physical size, and 300 DPI metadata. This still does not
provide a mutable browser framebuffer facade, and the external drawing-library
gap remains open.

## 2026-07-09 retained hardening evidence

The remaining open item is performance, not missing quality proof:

- `doc/09_report/gui_perf_benchmark_2026-07-09_cpu_base.md` records the retained
  8K external baseline at full `7680x4320`, default 300dpi, no screen-size
  reduction, checksum `sum32:135445232233405312`, nonzero pixel proof, CPU-SIMD
  runtime target, software-render-loop readback scope, and
  `fallback_used=false`.
- `scripts/check/check-cpu-simd-render-dpi-contract.shs` proves default 300dpi
  and an override DPI keep physical pixels unchanged with stable checksum.
- `doc/09_report/production_gui_web_backend_executed_evidence_2026-07-09_cpu_simd_alpha.md`
  proves CPU-SIMD color/transparency parity against software with zero differing
  pixels, alpha-quality hits, matching alpha checksums, and no tolerance/blur
  fallback.
- `doc/09_report/cpu_simd_engine2d_arch_matrix_2026-07-09.md` proves the
  Engine2D SIMD C kernels build/run for x86_64, AArch64, and RISC-V target
  binaries, with runtime owner compile coverage for RISC-V RVV.

The next implementation must therefore target a safe framebuffer owner facade
or a different measured framebuffer-fill reduction. It must not reduce viewport
size, change DPI semantics, route through GPU fallback, or accept checksum/color
drift as a speed win.

## 2026-07-09 browser-layout owner facade

Browser layout now routes full-frame framebuffer allocation through
`browser_layout_framebuffer_filled(base, width, height)`. The helper is the only
owner boundary for the proven compiler/native array-repeat fill path and keeps
the unsafe mutable Engine2D externs out of the renderer. This is a containment
step toward the native owner bridge: it centralizes the place where a future
typed native fill ABI can be installed without touching paint, GPU, DPI, or
quality semantics.

Focused evidence:

- `SIMPLE_LIB=src bin/simple test test/03_system/check/cpu_simd_render_scale_contract_spec.spl --mode=interpreter --clean`
  passed, including the guard that the renderer uses the safe owner fill facade
  and still excludes `rt_engine2d_simd_fill_u32`,
  `engine2d_simd_fill_row_u32`, and `rt_u32_alloc_filled`.
- A direct `bin/simple check` of the large renderer was attempted and exited
  `143` after the existing broad `SIMPLE_LIB=src` memory guard terminated the
  compile; no focused syntax failure was emitted before termination.

## 2026-07-10 deployment correction

The apparent `~765 ms` owner-fill bottleneck was traced to a stale deployed
runtime rather than the current owner facade or current array-repeat source.
The deployed `bin/simple` still implements `rt_array_repeat` as one
`rt_array_push` call per pixel. A direct 33,177,600-element probe measured
`762414us`, matching the retained 8K framebuffer initialization time.

Current C and pure-Simple runtime source already allocates repeat-private
uninitialized storage and fills it by doubling initialized spans with
`memcpy`. No packed-u32 framebuffer or new unsafe mutable ABI should be added
until that source is present in a fresh self-hosted binary and measured. The
owner facade remains the correct containment boundary.

---

## 2026-08-17 — REPRODUCED (still open at inspection) and FIXED (GPU slice worker E)

Classified by CONTENT against current source, not by commit ancestry.

### Root cause (confirmed live before the fix)

`src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`, in
`native_simd_pixel_evidence()`: the bit-exactness selfcheck opened with a
single hard-coded

    val count: i64 = 64

and validated exactly that one row length, then published the result as the
class-level claim `bit_exact: fill_exact and copy_exact` on
`NativeSimdPixelEvidence` — a type whose own docstring promises the kernels
"stayed bit-identical", unqualified.

Why 64 specifically cannot support that claim: on every SIMD level this
function accepts (`Neon`, `Avx2`, `Sse42`, `Rvv`) a 64-element `u32` row is an
exact whole number of vectors. So the selfcheck exercised **only the aligned
chunk path**. The one thing a vectorised fill/copy facade actually gets wrong
— the TAIL, where a remainder is left unfilled or written past the end — was
structurally unreachable by the evidence, at any count, forever.

That makes this the silent class rather than a coverage nit: the function does
not report "unverified beyond 64", it reports `bit_exact: true`, and callers
consume that as proof.

### Fix

The selfcheck now sweeps `[3, 17, 64, 65, 67]`:

- `3` — below one vector width (pure-tail, no aligned chunk at all)
- `17`, `65`, `67` — non-multiples straddling one or more whole vectors
- `64` — the original aligned case, retained rather than replaced, so prior
  coverage is not traded away

`fill_exact` and `copy_exact` now only stay true if EVERY count round-trips,
and the fill comparison checks against `color` directly instead of building a
parallel 64-element reference array that was itself fixed-size.

### Not addressed

This widens the *selfcheck*; it does not add a large-buffer or multi-row
(stride/pitch) case, so a 2-D blit defect that only appears across rows is
still out of reach of this evidence. Stated here rather than implied fixed.

### Verification status — HONEST GAP

The spec run for this change was queued behind a saturated `test-slot` queue
(a stage-3 bootstrap plus ~10 concurrent lanes) and had NOT produced a
`Results:` line by end of session. The change is a pure widening of an
existing in-source selfcheck and needs no build (`src/lib/**` is read as
source), but **it has not been executed**. Do not treat this row as verified
until `test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl` and
`simd_kernels_branch_coverage_spec.spl` are run green.
