# CPU and Vulkan web-renderer twins diverge by ~29% of pixels, and no budget is pinned

- **Filed:** 2026-09-13
- **Area:** ui / web renderer showcase (`std.gc_async_mut.gpu.browser_engine.simple_web_renderer`)
- **Status:** FIXED 2026-09-13 (see RESOLVED below); re-verified and closed 2026-11-13

## What was measured

Rendering the showcase catalog `overview` page at 160x90, once on `cpu_simd`
and once on `vulkan`, and comparing with the showcase's own comparator
`diff_argb` (`src/app/ui/chrome_showcase/pixel_diff.spl:45`):

```
DiffResult(pixels: 14400, reason: , mismatch: 4224, ok: true,
           max_delta: 37, mismatch_pct_x100: 2933)
```

That is **29.33%** of pixels differing by more than the per-pixel channel
tolerance, with a worst channel delta of 37.

The same comparison at 320x180, measured from the spec itself:

```
DiffResult(pixels: 57600, mismatch: 9384, ok: true,
           max_delta: 37, mismatch_pct_x100: 1629)
```

i.e. **16.29%**. The divergence is therefore size-dependent (29.33% at
160x90, 16.29% at 320x180) while the worst channel delta stays at 37, which
points at edge/anti-aliasing rules differing between the two rasterisers
rather than at a uniform colour-space offset. This is another reason a single
pinned percentage would not transfer between sizes. At 320x180 the two backends
likewise produce different frame digests (`18f09dab` cpu vs `cd562909`
vulkan). Each backend is individually deterministic: two renders on the same
backend produce identical digests.

The Vulkan lane genuinely ran on the GPU for these measurements
(`vk_init=true cpu_fallback=false dispatches_frame=1`), so this is a real
twin divergence, not a silent fallback.

## Why this is filed rather than asserted in a test

There is **no pinned CPU-to-Vulkan pixel budget anywhere in this repo**:

- `pixel_diff.spl`'s `TOLERANCE = 8` is a *per-channel delta* deciding whether
  one pixel counts as mismatched. It is not a pass threshold.
- `DiffResult.ok` is a well-formedness flag only: it is `false` solely for a
  dimension mismatch or an empty image (`pixel_diff.spl:45-62`).
- The CLI verdict (`pixel_diff.spl:184,210-213`) prints `worst=<pct>` and
  decides PASS/FAIL on *unreadable* pages only — the percentage is reported,
  never compared.
- `scripts/check/check-chrome-catalog-pixel-diff.shs` fails on zero-pixel
  renders, and otherwise forwards that verdict. It also compares Chrome
  against Simple, not CPU against Vulkan.

So `test/02_integration/ui/web_showcase/catalog_vulkan_twin_spec.spl`
captures the divergence as evidence and asserts only what is genuinely
pinned (both twins render, same geometry, non-blank, GPU lane not silently
falling back). Asserting an invented percentage there would manufacture a
threshold this repo has never agreed on.

## What is needed

An owner decision on whether the CPU and Vulkan web renderers are supposed to
be pixel twins:

1. If yes — this 29% divergence is a defect in one of the two backends, and a
   budget should be pinned so the twin spec can gate on it.
2. If no — the two are different renderers with different rasterisation
   rules, and that should be written down, with the twin comparison scoped to
   structural properties (which is what the spec asserts today).

Either way the number belongs somewhere enforceable; today it is measured by
nothing.

## RESOLVED 2026-09-13 — the twins were supposed to match, and now do

Both questions above are answered by the code itself rather than by an owner
decision: the CPU and Vulkan Engine2D backends ARE twins, and the divergence
was a single deviating implementation.

`backend_vulkan.spl:2917 draw_shadow_rect` painted a box-shadow as a flat
alpha rect padded by `blur_r` plus a blur. Every other backend already
delegated to the shared `emu_draw_shadow_rect`
(`backend_emu_adv.spl:283`), whose own comment (:276-279) documents the
flat-fill-then-blur shape as the *previous, wrong* implementation it replaced.
Vulkan was the sole holdout; it now delegates to the same function.

Measured after the fix with the same probes: `overview` at 160x90 goes
**29.33% -> 0.00%** (4224 -> 0 differing pixels, max_delta 37 -> 0), and all 8
catalog pages at 320x180 report 0 differing pixels.

The budget this record asked for is now pinned in
`catalog_vulkan_twin_spec.spl` (<= 0.5% of pixels, max_delta <= 8), with a
device-free formula pin in
`test/01_unit/lib/gpu/engine2d_shadow_rect_twin_formula_spec.spl`. Full
measurement record: `doc/10_metrics/ui/engine2d_twin_parity_2026-09-13.md`.

## 2026-11-13 closure (UI batch B, Linux aarch64, release/1.0.0 @ 35144b7f5e93)

Re-run on this host (Rust seed, 16G cgroup cap):

- `test/01_unit/lib/gpu/engine2d_shadow_rect_twin_formula_spec.spl`:
  `outcome=OK declared>=3 executed=3 passed=3 failed=0`, rc=0.
- `test/02_integration/ui/web_showcase/catalog_vulkan_twin_spec.spl`:
  `outcome=OK declared>=3 executed=3 passed=3 failed=0`, rc=0. Twin diff at
  320x180: `DiffResult(pixels: 57600, mismatch: 0, mismatch_pct_x100: 0,
  max_delta: 0)`; Vulkan digests `ad9bd0c6` twice.
- Source: `backend_vulkan.spl:3119` delegates to `emu_draw_shadow_rect`; the
  budget is pinned at `catalog_vulkan_twin_spec.spl:130-131`
  (`mismatch_pct_x100 <= 50`, `max_delta <= 8`).

Limit of this host's evidence, stated plainly: the census reported
`cpu_fallback=false` for the seven non-overview tabs but `dispatches_frame=0`
(the 2026-09-13 measurement had `dispatches_frame=1`), and the `overview` row
came back with empty census fields. So this run confirms the two lanes agree
pixel for pixel and that the spec's fallback guard did not trip; it does not
independently prove a GPU dispatch on this machine. The 0.00% GPU-dispatch
measurement remains the 2026-09-13 one in
`doc/10_metrics/ui/engine2d_twin_parity_2026-09-13.md`.

Both asks of this record are met (the divergence is fixed and a budget is
pinned and gated). `bug_db.sdn` row moved open -> fixed.
