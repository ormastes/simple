# A real catalog page renders 4.2x SLOWER on the Vulkan native-readback lane than on CPU software raster (macOS M4, 2026-09-12)

Status: **PARTLY FIXED, and the attribution below is PARTLY WRONG.** Read this
header before the body.

**Located (2026-09-12, per-op wall clock).** The unexplained term is the font
composite, not the raster. On css-layout.html at 300x253 the frame is 47.1 s
and `composite_font_batch` is **27.3 s of it across 5 calls**, of which
`_vulkan_font_pixels_to_bytes` is 19.0 s and `_vulkan_font_atlas_payload_digest`
is 8.2 s — two O(atlas) interpreted walks over a fixed 1024x1024 (4 MB) atlas,
re-run in full on every dirty batch. The SFFI upload they feed is 44 ms.

**Fix, and its OPEN pixel question:** `backend_vulkan_font.spl` keeps a host
byte mirror and repacks only `batch.dirty_rects`. At 300x253 that is
47,646 -> 35,389 ms (-25.7%) with the **PPM byte-identical** and the checksum
unchanged. **At 900x760 the frame checksum MOVES off the no-mirror baseline**
and three guard variants produced two values non-monotonically while the pack
counts never changed — see the metrics doc's variant table. Until that is
explained the incremental repack is NOT established as pixel-safe at 900x760,
and this record must not be read as claiming it is. Spec:
`test/02_integration/gpu/vulkan_font_atlas_incremental_repack_spec.spl` (10/10,
incl. a sabotage triple and the stale-mirror case).

**CORRECTION — the "~0.6 s per 1x1 alpha blend" figure below is WRONG.**
Measured directly: 76 one-pixel composites cost **99 ms TOTAL (1.3 ms each)**,
and all 187 rect dispatches cost 145 ms. The 0.6 s figure was inferred from a
run that moved two variables at once; no per-op cost was ever measured. The
whole "largest removable op population" section is therefore chasing ~0.2 s of a
47 s frame. **F14's held-back corner-sprite coalescing was NOT landed:** its
claimed -13.7% cannot be attributed to op cost that does not exist, so it would
have been landing an unexplained pixel-checksum move for nothing.

**Still open, quantified:** the payload digest (8.3 s / 5 calls) and the 2
remaining full repacks (7.8 s). Vulkan is now 1.44x cpu_simd at this size
(36.1 s vs 25 s), down from 2.7x — the parity target is MISSED. Measurements
and next steps:
`doc/10_metrics/ui/web_catalog_vulkan_per_op_attribution_macos_2026-09-12.md`.

Original text follows, retained for history.

Status: **OPEN.** The slowdown is measured and one large contributor is
quantified; the rest is NOT located in source. Nothing was changed in product
code: the one candidate fix is measured (-13.7%) and held back, and the census
added alongside it is read-only.

Binary, bracketed identical before and after every run:
`/Users/ormastes/simple/build/cargo-r2/release/simple`, `stat -f '%z %m'` =
`39368072 1789171430`. Run mode: `SIMPLE_2D_BACKEND=vulkan
SIMPLE_VK_READBACK=native SIMPLE_2D_BACKEND_STRICT=1
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 ... simple run`,
one at a time. Logs and probes: `build/perf/catalog_vulkan_2026-09-12/`
(gitignored). Page: `examples/06_io/ui/web_catalog/css-layout.html`, 40,960
bytes, 908 DOM nodes, 900x760.

The lane resolves for real — `backend_requested=vulkan backend_reported=vulkan`,
and `SIMPLE_2D_BACKEND_STRICT=1` would have failed the run otherwise.

## The headline, measured

| lane | size | cold frame | draws reaching the backend |
|---|---|---|---|
| `cpu_simd` (F12, same page) | 900x760 | 263,636 ms | — |
| **`vulkan` + `SIMPLE_VK_READBACK=native`** | **900x760** | **1,095,789 ms** | 550 |
| `vulkan` + native readback | 300x253 | 68,426 ms | 187 |

**The Vulkan native-readback lane is 4.2x SLOWER than CPU software raster on a
real catalog page.** That is the finding; everything below is why.

### It is not the readback, and it is not the draw count

`readbacks=3 readback_pixels=2052000` at 900x760 and `readbacks=1
readback_pixels=75900` at 300x253 — three and one full-surface readbacks per
frame respectively. (The 900x760 BEFORE run predates this counter; 3 is measured
on the after-run, at the same size and page.) A handful of native readbacks is
milliseconds, so the work in
`doc/08_tracking/bug/vulkan_readback_interpreted_unpack_dominates_frame_2026-09-12.md`
(two downloads per frame, interpreted per-pixel unpack) is genuinely fixed on
this tree, and `cpu_fallback_reason` is EMPTY — the native lane really ran.

Scaling and the after-run settle the rest, and they refute the obvious model.
900x760 has 9.01x the pixels of 300x253 and 2.94x the draws, and costs 16.0x the
time. A `draws x framebuffer_pixels` law fits those two points -- but it is a
two-parameter fit on two points, and the third point kills it: with 248 of the
one-pixel composites removed (302 ops) it predicts ~608 s and the run measured
945 s. `O(draws^2)` fits the first two equally well and fails the third the same
way. **Ops are not uniform, and no single law has been established.**

What the three points DO support, as a difference rather than a fit:

- removing **248 one-pixel image composites saved 150 s** at 900x760, i.e.
  **~0.6 s per 1x1 alpha blend** on this surface;
- the remaining **~945 s** sits on 286 opaque rect dispatches, **an unknown
  number of UNCOUNTED text dispatches**, 2 images and 3 readbacks.

That last point bounds everything else here. `text=0` in the census does not mean
no text was drawn: `Engine2D.draw_text` routes the Vulkan lane through the TYPED
font backend (`engine.spl:1938`, `vulkan_typed.draw_text` into
`backend_vulkan_font`), which touches none of the instrumented
`VulkanBackend` entry points. **The census is blind to text ops, so any per-op
cost attributed to opaque rects above is an UPPER bound.**

## The largest removable op population

Since cost is `ops x framebuffer`, cutting ops is worth exactly as much as cutting
the per-op term. The largest removable op population is three hops of
ordinary-looking code:

1. `emu_draw_rounded_rect` (`backend_emu.spl:365`) composes a filled rounded rect
   from `core.draw_rect_filled` calls: 3 bands plus 4 corner boxes. Its own
   comment already notes that on the Vulkan lane "every `draw_rect_filled` is a
   real dispatch", and the full-coverage run of each corner row was already
   coalesced into one span for exactly that reason.
2. `_emu_corner_box_aa` (`backend_emu.spl:387`) then emits the ANTI-ALIASED
   pixels — the ones whose coverage is between 0 and 256 — as **one
   `draw_rect_filled(px, py, 1, 1, c)` per pixel**. They cannot be run-coalesced
   the way the full-coverage run was, because each carries a different alpha.
3. `VulkanBackend.draw_rect_filled` (`backend_vulkan.spl:1006`) routes **any**
   colour with `alpha < 255` into `draw_image_blend` with a `[color; w*h]`
   array. For a 1x1 that is a one-pixel image. `_draw_image_composite_native`
   then does a staging-buffer acquire, a host pack, a `copy_to_buffer` upload,
   and a compute dispatch — **per anti-aliased pixel**.

So a rounded rect of radius `r` costs `3 + 4r` opaque dispatches and up to
`4 * r^2` full image-composite submissions. Measured on this page, those were
**260 of the 550 backend ops at 900x760** and **76 of 187 at 300x253** — i.e.
**41-47% of everything reaching the backend was a ONE-PIXEL image composite.**
Nothing about this is visible from the CPU lane, where a 1x1 alpha fill is a
handful of instructions.

This is the same defect CLASS as
`doc/08_tracking/bug/emu_shape_decomposition_emits_one_gpu_dispatch_per_pixel_2026-09-03.md`,
which fixed it for OUTLINES by run-batching collinear points. Anti-aliased
corners were left behind because a run of pixels with differing alpha is not a
rectangle — the missing move was not run-batching but **gathering into a sprite**.

### Two further CPU/host terms on this lane, named rather than fixed

- **`emu_draw_shadow_rect` (`backend_emu_adv.spl:283`) calls `core.read_pixels()`
  — a full GPU->host framebuffer readback — once per box-shadow**, then
  composites the blurred coverage field with one `draw_image` upload. It is
  already coalesced per element (it is NOT per pixel), but every shadowed
  element on the page pays a round trip of the whole 900x760 surface. Filed, not
  fixed: it needs a device-side separable blur, and no blur pipeline exists
  (`pipe_*` on `VulkanBackend` has no blur entry).
- **`emu_draw_image_blend` (`backend_emu_adv.spl:66`) does `core.read_pixels()`
  per call for any backend that is not named `cpu`.** On the Vulkan lane this
  path is reached only when `_draw_image_blend_native` fails, but when it is
  reached the per-pixel corner loop above becomes a full framebuffer readback per
  corner pixel. The census counter `cpu_fallback_reason` is the thing to read
  before trusting any measurement on this lane.

## Candidate fix, measured then backed out

`_emu_corner_box_aa` was changed to gather the partial-coverage pixels of a
corner into one `r x r` sprite composited with a single `core.draw_image_blend`,
leaving the full-coverage run on `draw_rect_filled` (that path packs the clip
rectangle into its dispatch). Measured: **1,095,789 -> 945,480 ms at 900x760
(-13.7%)**, `rect_alpha_1x1` 260 -> 0, and at 300x253 the page PPM was
**byte-identical** (`cmp` clean, same checksum).

**It is held back**: at 900x760 the frame checksum MOVED
(2936851399036017 -> 2936851411469080, ~12.4M over 684,000 pixels). The software
twin is provably identical (9/9 spec, incl. edge-straddling and clipped), and
`_emu_blend_over` and `sw_hline_blend` both reduce to the same `color.blend()`,
so the divergence is not blend arithmetic. It appears only at the size that also
has offscreen groups (`image=2`, `readbacks=3` vs `image=0`, `readbacks=1`).
**The divergence is not attributable to the coalescing**: that 900x760 run also
carried a second change (a zero-area band guard), so two variables moved in one
run. `rect_opaque` went 288 -> 286 at 900x760 and 111 -> 111 at 300x253, which
proves the guard was active ONLY in the diverging run, while the coalescing ran
the full Vulkan composite kernel at 300x253 and was byte-identical there. The
guard has since been reverted -- its stated benefit never manifested either
(`cpu_fallback=false` in the BEFORE census, with those zero-area dispatches
present, so the `rect-dispatch-failed` latch did not fire on the batching path).
Re-measuring the coalescing alone costs ~36 minutes and was not affordable here. The patch is kept at
`build/perf/catalog_vulkan_2026-09-12/corner_aa_batch.patch` (gitignored, so it
is a local artifact: regenerate it by rewriting `_emu_corner_box_aa` as described
above).

Why the pixels were expected not to change (and do not, on the software twin):

- An alpha-modulated 1x1 fill already IS a source-over blend of that one pixel,
  on every backend. On Vulkan both shapes call the same
  `_draw_image_composite_native`, which packs the framebuffer bounds and the clip
  rect into its push constants and clips PER PIXEL in the shader, so a sprite
  straddling an edge or a clip behaves exactly as the individual pixels did. On
  the software backend `sw_hline_blend` and the image-blend row kernel both
  reduce to the same `blend(src, dst)` (`backend_software.spl:1463` and `:920`),
  and the image path skips `alpha == 0` — which is precisely the old loop's
  "an empty pixel not at all".
- The pixels of a corner box are pairwise distinct, and disjoint from the three
  bands, so gathering them cannot reorder an overlapping write.

## Nothing changed in product rendering code

The census counters are read-only. No rasterizer behaviour was altered.

## Oracle

`test/02_integration/gpu/engine2d_rounded_rect_corner_batch_parity_spec.spl`
builds the expected frame from an INDEPENDENT re-derivation of the shared corner
coverage formula (the two helpers are written out in the spec, not imported, so a
formula bug cannot cancel itself out) replayed through the OLD per-pixel call
shape, and requires equality pixel for pixel. Cases: opaque, translucent, radius
3 / 8 / 20, a corner straddling the framebuffer edge, and a clipped box. Three
sabotage cases (wrong radius, wrong colour, empty frame) prove the comparison is
not vacuous.

## Measured

See `doc/10_metrics/ui/web_catalog_vulkan_native_lane_macos_2026-09-12.md`.

## Gaps

- The style engine prints `[rfm]`, `[font-inherit-trace]` and
  `[font-style-trace]` UNCONDITIONALLY on the hot path — thousands of lines per
  page render (815 `[rfm]` lines in the first 4,354 lines of one cold log). Those
  files are owned by another lane; the prints inflate BOTH the cpu_simd and the
  Vulkan numbers and should be level-gated.
- `cpu_fallback_*` on `VulkanBackend` is a one-shot latch (first reason only),
  not a per-reason census. The draw-kind counters added in this change are
  process-global module state for the same reason.
