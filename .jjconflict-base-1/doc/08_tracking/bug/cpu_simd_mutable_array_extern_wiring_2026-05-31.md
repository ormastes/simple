# CPU SIMD mutable array extern wiring

Status: Open.

Date: 2026-05-31

## Status

Open.

## Context

Phase 2 of the 2D rendering optimization plan added hosted C runtime entrypoints
for native CPU SIMD span operations:

- `rt_engine2d_simd_fill_u32`
- `rt_engine2d_simd_copy_u32`

These mutate `[u32]`-style runtime arrays in native execution. The current
interpreter extern bridge receives `Value` arguments by value and cannot safely
mutate the caller's `Value::Array(Arc<Vec<Value>>)` in place.

## Impact

`simd_kernels.spl` must keep using the pure Simple scalar/SIMD-compatible
implementation in interpreter mode. Wiring the new C entrypoints directly into
the public Simple `fill_span`/`copy_span` functions would either fail in the
interpreter with unknown externs or risk a native/interpreter behavior split.

## Required fix

Add a proven mutable typed-array extern bridge for interpreter mode, or add a
native-only dispatch mechanism that semantic analysis accepts without requiring
the interpreter to resolve and execute the native C symbol.

After that exists, route `fill_span` and `copy_span` through the native
entrypoints when the host reports a matching SIMD tier, and keep the existing
Simple loops as fallback/reference paths.

## 2026-07-06: facade dishonesty audit + honesty fix

An audit of the `cpu_simd` 2D render backend found that the "SIMD-backed CPU
renderer" claim was false — `cpu_simd` delivers scalar CPU on every arch:

- (a) `engine.spl:271-274` maps `cpu_simd` → `CpuBackend.create()`, identical to
  plain `cpu`. There is no distinct SIMD backend construction.
- (b) `CpuSimdSession` (`cpu_simd_session.spl`) is orphaned — it is referenced
  nowhere outside its own file, so no code path ever instantiates it.
- (c) `simd_kernels.spl` native rows are NEON-only gated
  (`_neon_pixel_rows_enabled`), so even a wired caller would skip the x86
  kernels entirely.
- (d) The x86 SSE2/AVX2 externs `rt_engine2d_simd_*_row_u32` ARE registered
  (`common/src/runtime_symbols.rs`) and implemented (AVX2 in
  `runtime_simd_dispatch.c`, SSE2 in `engine2d_simd_ops.rs`) — but they are
  unused. Genuinely wiring SIMD is therefore a real future task (route the
  orphaned session + x86 dispatch), not a contained fix.
- (e) Honesty fix applied: the `cpu_simd` probe text in `engine.spl` now reads
  "CPU renderer (alias of cpu; no live SIMD dispatch) always available" instead
  of the false "SIMD-backed CPU renderer" claim, with a code comment pointing
  here.

Related: the mutable-array extern layout blocker is tracked in sibling
`bug_simd_bulk_copy_blocked_by_spl_array_layout_2026-05-02.md`.

Status remains Open — the honesty fix corrects the claim; the underlying SIMD
wiring gap is still unaddressed.

## 2026-07-09: retained 8K Simple Web evidence

The retained Simple Web CPU-SIMD 4K/8K benchmark now routes through the real
layout renderer and proves the remaining bottleneck is full-frame framebuffer
allocation/fill, not parser, CSS, layout, or text glyph setup:

- 8K trace: `paint_ms=776`, total `779724us`, checksum
  `sum32:135445232233405312`.
- Normal retained 8K row after the text glyph inline optimization:
  `938678us`, checksum `sum32:135445232233405312`.
- External Node Canvas/Cairo comparison remains `80.201ms` p50 at the same 8K
  size, so the retained Simple row is still about `11.7x` slower.

Direct browser-layout attempts to use the current SIMD fill externs are still
blocked by this owner-boundary problem:

- `simd_fill_row` over the layout framebuffer reported
  `unknown extern function: rt_engine2d_simd_fill_u32`, changed checksum, and
  slowed 4K trace to `878028us`.
- `engine2d_simd_fill_row_u32` over a full framebuffer segfaulted at 4K.
- A safer experiment that routed `fb_rect`/`fb_rect_clip` row fills through
  `backend_software`'s existing `simd_fill_row` owner preserved 4K/8K checksums,
  but regressed 8K to `1543525us`, so it was reverted.

The smallest next real fix is still the same: add a proven mutable typed-array
write-back bridge, then route bulk `[u32]` clear/fill/readback through that
owner boundary. Browser-local SIMD fill shortcuts should remain rejected until
that bridge exists.

## 2026-07-09: public facade containment

The public `simd_fill_row` facade no longer calls the unsafe
`rt_engine2d_simd_fill_u32` mutable extern. On native-capable hosts it now uses
the already-proven return-row ABI (`rt_engine2d_simd_fill_row_u32`) and scatters
that row back into the caller's buffer; otherwise it uses the scalar fallback.
The interpreter's previous no-op shim for `rt_engine2d_simd_fill_u32` is also
unregistered, so direct mutable-fill use fails closed until a real write-back
bridge exists.

Focused evidence:

- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl --mode=native --clean`

Both modes pass 19 examples. This contains the missing-extern failure for public
row fill callers, but it does not close the full-frame 8K performance blocker:
the mutable typed-array write-back bridge is still required before browser
layout can safely bulk-fill a full framebuffer through the native mutable
extern.

## 2026-07-20: re-audit + re-applied honesty fix (previous 2026-07-06 text lost)

Re-audited per lane SIMD-HONESTY (`doc/03_plan/ui/wm_aqua_glyph/next_wave_2026-07-20.md`
item #6(a)). The 2026-07-06 "honesty fix" entry above claimed `engine.spl`'s
`cpu_simd` probe text had been changed to "CPU renderer (alias of cpu; no live
SIMD dispatch) always available", but the current tree still had the original
dishonest "CPU SIMD row provider available" — the earlier fix was reverted at
some point (this repo has documented sync/rebase clobber incidents; not worth
bisecting, the fix is small and reapplied here with a spec regression guard).

**Confirmed still true**: no real SIMD implementation is wired for the plain
`cpu_simd` render lane. `CpuBackend.create_simd()` (`backend_cpu.spl`) builds
the identical scalar `SoftwareBackend` as `CpuBackend.create()`; its
`RenderBackend.name()` already honestly returns `"cpu"`. The x86 SSE2/AVX2 row
externs exist in the runtime (`common/src/runtime_symbols.rs`,
`runtime_simd_dispatch.c`, `engine2d_simd_ops.rs`) but remain unused —
genuinely wiring them is out of scope here (touches `src/runtime`/the Rust
seed, which this fix does not touch) and is not a small contained change per
the 2026-07-06 audit (d). **Chose the honest-alias path, not the wire path.**

Changed (pure-Simple, `src/lib/**` only):

- `src/lib/gc_async_mut/gpu/engine2d/engine.spl` — `probe_backend("cpu_simd")`
  success message restored to honestly say "CPU renderer (alias of cpu; no
  live SIMD dispatch) always available" (was "CPU SIMD row provider
  available").
- `src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl` —
  `_strict_probe_backend(BACKEND_CPU_SIMD)` (used by `BackendProber`/
  `compute_dispatch.spl`) no longer implies the detected host SIMD feature is
  actively dispatched; message now: "CPU renderer (alias of cpu; no live SIMD
  dispatch); host feature detected=<level>" (was "CPU SIMD row ABI available;
  active feature=<level>").
- `src/lib/gc_async_mut/gpu/engine2d/helpers_availability.spl` —
  `backend_display_name("cpu_simd")` now returns "CPU (SIMD alias, no live
  SIMD dispatch)" (was bare "CPU SIMD"); `feature_gate_description("cpu_simd")`
  now returns "No external dependencies; scalar CPU path (no live SIMD
  dispatch)" (was "...uses CPU SIMD when available").
- The `"cpu_simd"` name itself is kept as an accepted config/env alias
  (`SIMPLE_2D_BACKEND=cpu_simd` still resolves and initializes) for backward
  compatibility — only the reported provenance text changed.

Spec extended (not weakened — two new discriminating cases, all existing cases
kept): `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_env_backend_select_spec.spl`
adds:
1. "requested+honored" — `SIMPLE_2D_BACKEND=cpu_simd` is honored (name kept for
   compat) and `backend_display_name`/`feature_gate_description` of the
   resolved name must contain "no live SIMD dispatch" and must not equal/contain
   the old dishonest strings.
2. "requested+fallback" — `SIMPLE_2D_BACKEND=cpu_simd_x86` (an arch-specific
   variant Engine2D's own `probe_backend` does not implement) always falls
   back through auto-probe; the shared `cpu_simd` descriptor queried directly
   must still report honestly regardless of which backend wins the fallback.

Evidence: `bin/simple test <spec>` single-file runs currently hang/timeout
system-wide on the deployed release binary (`bin/release/x86_64-unknown-linux-gnu/simple`,
a stale Rust seed — "WARNING: this Rust-built Simple binary is a bootstrap
seed only", `Simple Language v1.0.0-beta`) — this is the pre-existing,
already-documented `deployed_seed_test_runner_init_hang_2026-07-17.md` defect,
unrelated to this change (confirmed by letting one single-file `simple test`
invocation for this exact spec run for 2m17s to an internal
`ERROR: test daemon timed out`). Per that bug's own note, `bin/simple run` is
unaffected, so it was used as the fallback runner:

```
SIMPLE_LIB=src bin/simple run test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_env_backend_select_spec.spl
```

Verbatim result:

```
Engine2D config/environment backend selection
  ✓ reads the SIMPLE_2D_BACKEND override
  ✓ honors an available override backend (software always initializes)
  ✓ falls through to auto-probe when the override is unavailable
  ✓ auto-selects a non-empty backend with no override
  ✓ requested+honored: SIMPLE_2D_BACKEND=cpu_simd is honored by name (compat) but reports itself honestly as a scalar-CPU alias
  ✓ requested+fallback: an arch-specific SIMD request the engine cannot honor falls back without ever claiming live SIMD

6 examples, 0 failures
```

**Status remains Open.** This is a provenance-honesty fix only — the
underlying SIMD wiring gap (mutable typed-array write-back bridge, orphaned
`CpuSimdSession`, unused x86 SSE2/AVX2 externs) is still unaddressed and
tracked by this same doc and sibling
`bug_simd_bulk_copy_blocked_by_spl_array_layout_2026-05-02.md`.
