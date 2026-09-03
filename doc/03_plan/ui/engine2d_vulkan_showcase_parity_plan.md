# Engine2D ↔ C Vulkan showcase parity: perf matrix, bit-level diff, feature map

- **Date:** 2026-09-03
- **Status:** plan; phase 0 (census) COMPLETE and recorded below
- **Branch/worktree:** `perf/vulkan-2d-c-benchmark` in `/private/tmp/simple-vkbench`
- **Builds on:** `doc/01_research/local/2d_rendering_perf_dma_alignment_soa_async.md`
  (fix list items 1-5), `doc/01_research/domain/2d_renderer_gpu_offload_patterns.md`
- **Measured baseline:** `doc/02_requirements/nfr/engine2d_vulkan_2d_perf.md`
- **Harness:** `bench/vulkan_2d_c/`, `scripts/check/check-vulkan-2d-c-compare.shs`

## Why this plan exists

The whole-frame ratio (Simple 59-79 vs C's 1000) says the lane is slow but not
WHICH primitive is slow, and it cannot say whether Simple draws the same
PICTURE. Those are different questions and need different instruments: a
per-primitive perf matrix, and a bit-level pixel diff. This plan builds both on
one shared scene definition, so a primitive is measured and diffed from the
same source of truth.

## Phase 0 — census (DONE)

Classification of every drawing entry point in
`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`, by reading each method
body (not by name). 34 primitives:

| Class | n | Members |
|---|---|---|
| **GPU-native** | 13 | clear, draw_rect, draw_rect_filled, draw_line, draw_circle_filled, draw_triangle_filled, draw_gradient_rect, draw_image, draw_image_blend_checked, draw_shadow_rect, draw_text, draw_text_bg, set_clip |
| **CPU `emu_*`** | 16 | draw_circle, draw_arc, draw_bezier, draw_ellipse, draw_ellipse_filled, draw_polygon_filled, draw_polyline, draw_rounded_rect, draw_rounded_rect_outline, draw_rect_thick, draw_circle_thick, draw_triangle_outline, draw_gradient_rect_h, draw_radial_gradient, draw_image_scaled, draw_image_transform |
| **Forced full readback per call** | 5 | draw_rect_blend, draw_image_blend, draw_image_scaled_blend, draw_blur_rect, draw_rect_blend_mode |

Two findings that set the agenda:

1. **Only 13 of 34 primitives actually run on the GPU.** The "vulkan" backend
   name describes the lane, not the work. `draw_circle_filled` is GPU while
   `draw_circle` is CPU — an asymmetry no caller can see.
2. **5 primitives force a device→host round trip PER CALL**, via
   `_flush_for_host_fallback`. A full-frame refresh measures ~2.4 ms, so a
   single `draw_rect_blend` costs more than an entire 64-rect GPU frame.
   This is research fix-list items 3 and 4, still open, now with a per-call
   cost attached.

## Comparison tiers

Bit-exactness is only promised where it is achievable; anything else would be a
claim the harness cannot keep.

| Tier | Meaning | Applies to |
|---|---|---|
| **bit-exact** | every pixel identical to C | clear, rect fill/outline, gradient rect, triangle fill, set_clip |
| **tolerance** | diff-pixel count, max channel delta, first-diff coordinate | lines, circles, ellipses, arcs, beziers, polygons, blends — C's rasterizer differs from `emu_*` by construction; the diff still catches wrong position, wrong colour, missing shape |
| **perf-only** | timed, not pixel-compared | text (bit-exact C text means porting the font rasterizer), image transforms, engine composition |

## Workload identity (blocks the bit-diff)

The two legs currently render DIFFERENT rect sets: C uses an unsigned `u64`
xorshift; the Simple bench uses the same seed constant as `i64` (negative),
masks with `0x7FFFFFFFFFFFFFFF` and sign-flips. Coverage 60.1% vs 63.9%.
Tolerable for a throughput ratio, **fatal for a bit diff**.

Fix: generate the scene table ONCE and commit it as literal data both legs
load. Not a port of xorshift into `i64` — arithmetic-vs-logical shift and
unsigned modulo are exactly where that would silently diverge again. A
committed table is bit-identical by construction and self-evidently so.
`main.c` stays verbatim (it is the upstream reference); the table lands beside
`vk2d_bench.c`.

## Phases

- **P1 Shared scene table.** Emit `scenes.txt` (one primitive + args per row),
  loaders in C and Simple. Re-run the existing 64-rect bench off the table and
  confirm the two legs' checksums now MATCH — that is the end-to-end proof the
  bit-diff mechanism works, before any new primitive is added.
- **P2 Simple-vs-Simple parity runner (no C required).** Run one scene on the
  `cpu` and `vulkan` backends and bit-diff the readbacks. The 16 `emu_*`
  primitives share CPU code across both backends, so any divergence is confined
  to the 13 GPU-native ones — a small, high-value surface, and the cheapest
  rendering-bug detector available. **Do this before the C ports.**
- **P3 Per-primitive perf matrix.** One scene per primitive, both legs, into
  `evidence.env` rows reusing the existing fail-closed `skipped` semantics.
  The harness must bake in what is currently done by hand: SIGBUS retry with
  attempt count, same-run pairing with range reporting (machine swing measured
  at ~36%), and a JIT-mode assertion so an interpreter fallback cannot silently
  poison a row.
- **P4 Showcase covering all ~45 Engine2D primitives.** Simple side exercises
  every primitive (a scene list is cheap); the C side implements only what the
  tier table requires. Existing `src/app/ui_showcase` drives DrawIR, not the
  primitive surface, so this is new; wire into those hosts only after the
  bench-side scenes work.
- **P5 Fixes, in measured order.** Named already: the 5 forced-readback
  primitives (defer the flush / GPU-native alpha blend — research items 3, 4),
  and the per-element copy loop at `backend_vulkan.spl:1504` (`rt_array_copy`
  exists in the runtime but has no Simple-level surface). Both are already
  flagged mechanically by the `gpu_2d_perf` lint (G2DP001/G2DP002).

## Non-goals

Porting the font rasterizer or the `emu_*` algorithms to C. Full C
implementations of all 45 primitives. Changing the NFR budget to make the gate
pass.
