# Engine2D ↔ C Vulkan showcase parity: perf matrix, bit-level diff, feature map

- **Date:** 2026-09-03
- **Status:** P0, P1, P2, P4 COMPLETE with measured evidence (below); P3 partial; P5 open
- **Branch/worktree:** `perf/vulkan-2d-c-benchmark` in `/private/tmp/simple-vkbench`
- **Builds on:** `doc/01_research/local/2d_rendering_perf_dma_alignment_soa_async.md`
  (fix list items 1-5), `doc/01_research/domain/2d_renderer_gpu_offload_patterns.md`
- **Measured baseline:** `doc/02_requirements/nfr/engine2d_vulkan_2d_perf.md`
- **Harness:** `test/05_perf/bench/vulkan_2d_c/`, `scripts/check/check-vulkan-2d-c-compare.shs`

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
| **GPU-native** | 12 (was 13; see census correction) | clear, draw_rect, draw_rect_filled, draw_line, draw_circle_filled, draw_triangle_filled, draw_gradient_rect, draw_image, draw_image_blend_checked, draw_shadow_rect, draw_text, draw_text_bg, set_clip |
| **CPU `emu_*`** | 16 | draw_circle, draw_arc, draw_bezier, draw_ellipse, draw_ellipse_filled, draw_polygon_filled, draw_polyline, draw_rounded_rect, draw_rounded_rect_outline, draw_rect_thick, draw_circle_thick, draw_triangle_outline, draw_gradient_rect_h, draw_radial_gradient, draw_image_scaled, draw_image_transform |
| **Forced full readback per call** | 6 (incl. draw_shadow_rect) | draw_rect_blend, draw_image_blend, draw_image_scaled_blend, draw_blur_rect, draw_rect_blend_mode |

Two findings that set the agenda:

1. **Only 13 of 34 primitives actually run on the GPU.** The "vulkan" backend
   name describes the lane, not the work. `draw_circle_filled` is GPU while
   `draw_circle` is CPU — an asymmetry no caller can see.
2. **5 primitives force a device→host round trip PER CALL**, via
   `_flush_for_host_fallback`. A full-frame refresh measures ~2.4 ms, so a
   single `draw_rect_blend` costs more than an entire 64-rect GPU frame.
   This is research fix-list items 3 and 4, still open, now with a per-call
   cost attached.

## MEASUREMENT REFRAME (2026-09-03) — read before using any per-primitive number

Under frame batching (the default), descriptor sets are cached per pipeline and
dispatches accumulate in ONE command buffer, executing only at a flush.
Therefore **every per-primitive vulkan timing in this document measures
CPU-side command RECORDING, not GPU execution.** The GPU work lands later, in
`submit_batch` or in the next forced flush.

Evidence: 12,226 dispatches were recorded between one flush and the next; that
flush cost 344,754 us => ~28 us per dispatch, cross-checked against a second
flush at 204,682 us / 8,553 dispatches => ~24 us.

Three consequences:

1. **`submit_batch` at 84,818x is confirmed deferred execution, not a
   regression** — and its backlog is overwhelmingly the emu tier's per-pixel
   output. It is emu-tier cost wearing another label.
2. **The emu tier is WORSE than its logged 42.7x**, because its GPU execution
   is excluded from its own rows and charged to `submit_batch` instead.
3. A per-primitive row can only be compared to another per-primitive row, never
   read as wall-clock cost of that primitive.

### The ~330 ms one-time cost is LOCATED

It is `_flush_for_host_fallback` DRAINING THE ACCUMULATED BATCH, not any
allocation. Instrumented split at `backend_vulkan.spl:1601`:
call 1 `flush_us=204682 emu_us=3660`; call 2 `flush_us=294 emu_us=3806`. ~94%
is emu backlog drain. Reordering the readback tier ahead of the emu tier in the
showcase drops first-blend 274 ms -> 19 ms.

The three allocation hypotheses recorded earlier as "disproved" were disproved
for the right reason: they were chasing a ghost. A residual first-submit warmup
of ~12-82 ms (2 samples, wide) is NOT pinned; suspected MoltenVK pipeline/MSL
compile.

### CENSUS CORRECTION

`draw_shadow_rect` was classified GPU-native. It is not: `backend_vulkan.spl:1671`
is `draw_rect_filled` + **`draw_blur_rect`**, and `draw_blur_rect` is
forced-readback tier. Warm (readback tier run first) it measures **7,623 us vs
cpu 7,115 us — parity**; the reported 2.5x was first-flush warmup attribution.

Corrected census: **12 GPU-native, 16 CPU `emu_*`, 6 forced-readback.**

### `present` is an inherent limitation, not a defect

`present` 2,317 us vs cpu 9 us is the full device->host mirror refresh
(`SIMPLE_VK_PRESENT_TRACE`: `flush_us=8`, `refresh_us=3587`). The CPU backend's
framebuffer IS host memory, so it has nothing to copy. This vanishes only under
a real swapchain present (`presentation_swapchain=0` in these runs). **Do not
"fix" it.**

### Unresolved

`draw_text_bg` 277 us vs cpu 124 us is stable across runs (277/293/463/518/525)
so it is real, but no cause was located. Absolute cost 150-400 us; low stakes.

### JIT fragility (affects how this bench must be edited)

Any edit to the bench's `main()` beyond a pure statement reorder de-JITted it
~500x, and the unmodified file once failed 12 consecutive attempts. The
JIT-mode assertion proposed for the perf matrix is validated as NECESSARY, not
merely nice to have.

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
- **P5 Fixes, in measured order.** FIRST ONE LANDED:
  `emu_draw_circle_thick` converted from a per-pixel bounding-box scan to
  span form — vulkan **9,955 us -> 1,176 us (8.5x)**, cpu 122 -> 31 us,
  pixel-identical (verified against a pre-change golden, since the parity gate
  cannot validate a shared-`emu_*` rewrite: both backends change together).
  30 per-pixel sites remain in `backend_emu.spl`. Named already: the 5 forced-readback
  primitives (defer the flush / GPU-native alpha blend — research items 3, 4),
  and the per-element copy loop at `backend_vulkan.spl:1504` (`rt_array_copy`
  exists in the runtime but has no Simple-level surface). Both are already
  flagged mechanically by the `gpu_2d_perf` lint (G2DP001/G2DP002).

## Results (2026-09-03)

### P1 — shared scene table: DONE
`test/05_perf/bench/vulkan_2d_c/scenes.txt`, verified byte-identical to C's own generator
(`VK2D_DUMP_RECTS`, 64/64 rows). Both legs now agree exactly:
`nonclear` 288504 = 288504, `checksum` 10460147 = 10460147 (previously 288504
vs 306818 and 10460147 vs 11073548).

### P2 — bit-level diff: DONE, and Simple MATCHES C
`scripts/check/check-vulkan-2d-bit-diff.shs`:
**PASS — 1,920,000 bytes compared, 0 differing.** Simple's Vulkan output is
byte-identical to the C Vulkan reference for clear + 64 rect fills. Calibrated
against a single flipped bit.

### P4 — feature showcase + backend parity: DONE for the exercised surface

`test/05_perf/bench/vulkan_2d_c/feature_showcase.spl` (**38 timed marks**, ~32 distinct draw
primitives of the 34-primitive census) +
`scripts/check/check-engine2d-backend-parity.shs`:
**PASS — 1,920,000 bytes across 38 primitives, 0 differing** between the cpu
and vulkan backends.

Includes `draw_text`/`draw_text_bg`, which matter most here: they are
GPU-native (vulkan SPIR-V glyph path) versus the cpu rasterizer, so unlike the
shared `emu_*` primitives they are a genuine divergence candidate. Verified
NON-VACUOUS — the text band carries 1,696 non-clear pixels, so the diff is
comparing rendered glyphs, not two blank regions.

**Scope of the claim:** no divergence **in the primitives exercised**. Not
covered yet: the `draw_engine`/`draw_ir_*` composition family and
`draw_software_offscreen_opacity_consume`. The mechanism argument (16 `emu_*`
primitives share CPU code, so divergence can only be in the ~13 GPU-native
ones) is sound, but only ~9 of those 13 have actually been run through the
gate.

### P3 — per-primitive perf matrix: the systemic finding

**CORRECTION (2026-09-03, from the full 38-row table).** An earlier revision
of this section said "every primitive is slower on the vulkan backend". That
was wrong: it was read off a top-16-by-ratio listing, which by construction
showed only the losers. The full table splits cleanly by tier, and the GPU
WINS where it is actually used:

| Tier | n | cpu total | vulkan total | ratio | vulkan faster on |
|---|---|---|---|---|---|
| GPU-native | 12 | 11,826 us | 19,062 us | 1.6x | **8 of 12** |
| CPU `emu_*` | 18 | 5,408 us | 230,722 us | **42.7x** | 0 of 18 |
| forced-readback | 6 | 20,312 us | 292,303 us | 14.4x | 3 of 6 |

Examples of the GPU winning: `clear` 3,616 -> 108 us (33x faster),
`draw_triangle_filled` 408 -> 15 us (27x), `draw_line` 128 -> 17 us (7.5x),
`draw_circle_filled` 81 -> 19 us (4.3x), `draw_rect_filled` 99 -> 34 us (2.9x).

So the finding is sharper than "vulkan is slow": **the GPU lane is fast for the
13 primitives it actually implements and catastrophic for the 18 that decompose
to per-pixel dispatches.** `submit_batch`+`present` (12 us cpu vs 347,071 us
vulkan) is deferred execution, not a regression — it is where the batched
dispatches actually run, so it must not be read as a per-primitive cost.

The losers, all `emu_*` or forced-readback:

| Primitive | cpu | vulkan | ratio |
|---|---|---|---|
| whole showcase | 32 ms | 449-513 ms | ~16x |
| draw_circle | 11 us | 1,590 us | 144x |
| draw_circle_thick | 98 us | 9,062 us | 92x |
| draw_radial_gradient | 774 us | 63,846 us | 82x |
| draw_ellipse | 23 us | 1,689 us | 73x |
| draw_bezier | 40 us | 2,200 us | 55x |
| draw_arc | 77 us | 2,012 us | 26x |

**Those all run the SAME `emu_*` CPU code on both backends.** Identical code,
two orders of magnitude apart. The cost is therefore not in the primitives but
in the per-call host/device synchronisation wrapped around them on the vulkan
lane. That is the target for P5, and it is a bigger lever than any individual
primitive.

### Root cause of the systemic gap (found 2026-09-03)

`emu_*` does not write pixels — it decomposes shapes into the backend's own
`draw_rect_filled`, and for outlines that is **one 1x1 rect per pixel** (31
such sites in `backend_emu.spl`). On cpu that is a memory write; on vulkan it
is a GPU compute dispatch. An r=35 ring is ~1021 dispatches. Full record:
`doc/08_tracking/bug/emu_shape_decomposition_emits_one_gpu_dispatch_per_pixel_2026-09-03.md`.

### Correction worth keeping

`draw_rect_blend` first measured at 351 ms for one call — nearly the whole
showcase, and it would have been the headline. A second identical call costs
4.1 ms (79x cheaper), so that is ONE-TIME initialisation, not per-call cost.
Steady state for the forced-readback tier is ~4 ms/call (still ~5x a whole
64-rect GPU frame). The one-time cost is reproducible but its site is **not
isolated**: staging-buffer allocation (7 us), per-frame array allocation
(351 us) and the `_pixels_to_bytes` upload (trace never fired on this path)
were each measured and disproved. Recorded as open rather than guessed.

## Non-goals

Porting the font rasterizer or the `emu_*` algorithms to C. Full C
implementations of all 45 primitives. Changing the NFR budget to make the gate
pass.
