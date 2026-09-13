# Engine2D CPU <-> Vulkan twin parity: the box-shadow formula divergence

- **Measured:** 2026-09-13, macOS arm64 host with a real Vulkan device
  (`vk_init=true cpu_fallback=false dispatches_frame=1` on every run below --
  no run in this record was served by a silent CPU fallback).
- **Runner:** `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=900
  build/cargo-r2/release/simple run <probe>`
- **Comparator:** `diff_argb` (`src/app/ui/chrome_showcase/pixel_diff.spl:45`),
  per-channel `TOLERANCE=8`. It compares RGB; an alpha-only difference is not
  counted, which the budget below inherits.
- **Supersedes:** the "no budget exists" conclusion in
  `doc/08_tracking/bug/web_cpu_vulkan_twin_pixel_divergence_unbudgeted_2026-09-13.md`.

## Classification of the differing pixels

The divergence was ONE op class, not a spread. The mismatch mask at 160x90 on
`overview` is a frame-shaped band -- a top bar plus left and right margins
around the content card -- and every sampled differing pixel showed the same
signature: CPU `0xFFEDEDFF`, Vulkan `0xFFDDDDF0`, a uniform -16/-16/-15 offset,
with `max_delta` fixed at 37 across both measured sizes.

| class | evidence | differing pixels attributed |
|---|---|---|
| box-shadow (`draw_shadow_rect`) | one non-1x1 alpha rect per frame, `x=6 y=12 w=148 h=2336 color=0x1f1e293b`, emitted on the Vulkan lane and on NO other lane | all of them |
| text glyphs | `text=0` in the lane census; glyphs reach the device as sub-16px image blends that were byte-identical between the twins | 0 |
| rect edges / AA, gradients, image sampling, blur/glass | no residual after the shadow fix (0 differing pixels on all 8 pages) | 0 |

Attribution method: the per-op census counters in `backend_vulkan.spl:3029-3072`
plus a temporary trace at the alpha-rect entry on BOTH lanes. The decisive
observation is that the CPU lane never received the op at all -- neither
`SoftwareBackend.draw_rect_filled` nor `draw_rect_blend` saw a non-1x1 alpha
rect for the whole frame -- so this was never an arithmetic difference in
`blend()`; the two backends were painting different geometry.

`cpu` and `cpu_simd` were verified byte-identical first (`mismatch=0
max_delta=0`), so the reference twin is unambiguous.

## Root cause

`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:2917` -- `draw_shadow_rect`
painted a box-shadow as a FLAT alpha rect padded by `blur_r`
(`draw_rect_filled(sx - blur_r, sy - blur_r, w + 2*blur_r, h + 2*blur_r, color)`)
followed by `draw_blur_rect`.

Every other backend already delegated to the shared
`emu_draw_shadow_rect` (`src/lib/gc_async_mut/gpu/engine2d/backend_emu_adv.spl:283`),
which rasterises the shadow as an alpha COVERAGE field over a region padded by
`2*blur_r`, blurs that coverage with a triple 1-D box blur
(`_emu_shadow_profile`, :262), and composites the shadow colour through it:
`backend_webgpu.spl:644`, `backend_intel.spl:474`, `backend_opengl.spl:304`,
`backend_baremetal.spl:516`, and `backend_metal.spl:2383` via its software
mirror. Vulkan was the sole holdout.

That flat-band shape is not merely "a different approximation": the comment at
`backend_emu_adv.spl:276-279` documents it as the *previous, wrong*
implementation the shared function replaced, because blurring a uniformly
filled region returns the same uniform region and the shadow gets no edge
falloff at all. So the deviating side is not a matter of convention -- Vulkan
had kept a formula the reference had already retired.

**Fix:** Vulkan's `draw_shadow_rect` now flushes for host fallback and calls
`emu_draw_shadow_rect`, exactly as its neighbouring `draw_blur_rect` already
did. No kernel changed, so no SPIR-V was regenerated.

## Per-page divergence, before and after

8 catalog pages at 320x180, `cpu_simd` vs `vulkan`, percentages are
`mismatch_pct_x100 / 100`.

| page | before | after |
|---|---|---|
| overview | 16.29% (9384 px, max_delta 37) | 0.00% (0 px, max_delta 0) |
| html | 16.29% (9384 px, max_delta 37) | 0.00% |
| css-layout | 16.29% (9384 px, max_delta 37) | 0.00% |
| css-paint | 16.29% (9384 px, max_delta 37) | 0.00% |
| forms-media | 16.29% (9384 px, max_delta 37) | 0.00% |
| animation | 16.29% (9384 px, max_delta 37) | 0.00% |
| evidence | 16.29% (9384 px, max_delta 37) | 0.00% |
| tab-bar | 0.00% (already matched -- this page has no shadowed card) | 0.00% |

Seven of the eight pages diverged by exactly the same pixel count, which is
itself evidence for the single-op story: the offending shadow is the catalog
shell's card, identical on every page that has one. `tab-bar` has no such card
and was already a match before the fix -- a page that was ALREADY green is the
control this measurement needed.

`overview` at 160x90: **29.33% -> 0.00%** (4224 -> 0 differing pixels,
`max_delta` 37 -> 0), reproducing the filed bug's number exactly and then
closing it.

The residual is ZERO, not a tolerated float-ULP band: the shadow is composited
in integer arithmetic on the host on both lanes, so there is nothing left to
diverge.

## Budget pinned

- `test/02_integration/ui/web_showcase/catalog_vulkan_twin_spec.spl` now
  asserts `mismatch_pct_x100 <= 50` (0.5% of pixels) and `max_delta <= 8`.
  The ceiling is deliberately above the measured 0.00% so an unrelated
  sub-pixel lane change is not a false red, while the 16-29% shadow divergence
  cannot return unnoticed.
- `test/01_unit/lib/gpu/engine2d_shadow_rect_twin_formula_spec.spl` is the
  device-free half: it pins the shared coverage formula by asserting the
  property that discriminates it from any flat-band approximation -- coverage
  falls off monotonically outward. It needs no GPU.

## Cost this fix accepts

One extra full-surface host readback per shadowed page on the Vulkan lane
(`overview` at 160x90: `readbacks=1 -> 2`, `image=0 -> 1`). This is the same
boundary crossing `draw_blur_rect` on this backend already performs. It is
recorded, not hidden: a device kernel could remove it, but it would first have
to reproduce `_emu_shadow_profile`'s triple box blur bit-exactly, and a kernel
that is merely close would reintroduce exactly the divergence this record is
about.

## 900x760, and the one residual that remains

Measured after the fix, same probes, `cpu_simd` vs `vulkan`:

| page (900x760) | after |
|---|---|
| overview | 0.00% (0 differing pixels, max_delta 0) |
| css-layout | 0.0044% (**30** differing pixels of 684,000, max_delta 116) |

The `css-layout` residual is real and is NOT claimed as fixed. 30 pixels with a
worst channel delta of 116 is a handful of hard-edged pixels, not a field
offset -- the signature of a one-pixel geometry or glyph-edge difference that
only becomes visible at this resolution, and it is absent at 320x180 and
160x90. It is inside the pinned 0.5% budget by three orders of magnitude, so
the budget does not hide it: anything that grows it toward 0.5% still fails.
Locating it needs a 900x760 mask run per op class, which did not fit in this
lane's budget; that is the named follow-up, not a silent tolerance.

`overview` at 900x760 reaching exactly 0 is what makes the residual
attributable to `css-layout`'s own content rather than to the shell both pages
share.
