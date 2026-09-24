# Web catalog on the Vulkan native-readback lane, macOS M4 (2026-09-12)

Binary `/Users/ormastes/simple/build/cargo-r2/release/simple`, `stat -f '%z %m'`
= `39368072 1789171430`, bracketed identical before and after every run.
`SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native SIMPLE_2D_BACKEND_STRICT=1
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0`, one run at a time.
Page `examples/06_io/ui/web_catalog/css-layout.html` (40,960 bytes, 908 nodes).
Logs/probe: `build/perf/catalog_vulkan_2026-09-12/` (gitignored). The lane is
proven: `backend_reported=vulkan`, strict mode would have failed otherwise, and
`cpu_fallback_reason` is empty on every row.

## Cold frame

| lane | size | cold ms | backend ops | 1x1 alpha blends | readbacks |
|---|---|---|---|---|---|
| `cpu_simd` (F12, same page, other tree) | 900x760 | 263,636 | — | — | — |
| **vulkan + native readback** | **900x760** | **1,095,789** | 550 | 260 | 3\* |
| vulkan + native readback | 300x253 | 68,426 | 187 | 76 | 1 |

\* the 900x760 BEFORE run predates the readback counter; 3 is measured on the
after-run at the same size and page (`readback_pixels=2052000`).

**The Vulkan lane is 4.2x slower than CPU software raster on this page.**

## What dominates — and what is NOT established

Not readback (a handful of NATIVE readbacks is milliseconds; the two-download /
interpreted per-pixel unpack defect is genuinely fixed on this tree). Not draw
count (900x760 carries 2.94x the draws of 300x253 and costs 16.0x the time).

**No cost law is established, and the obvious one is refuted.**
`draws x framebuffer_pixels` fits the two before-points, but that is a
two-parameter fit on two points and the after-run kills it: at 302 ops it
predicts ~608 s and measured **945 s**. `O(draws^2)` fits the same two points and
fails the third identically. Ops are not uniform.

What the three points support as a DIFFERENCE, not a fit:

- removing **248 one-pixel image composites saved 150 s** at 900x760 —
  **~0.6 s per 1x1 alpha blend** on that surface;
- the remaining **~945 s** sits on 286 opaque rect dispatches, an unknown number
  of **UNCOUNTED text dispatches**, 2 images and 3 readbacks.

`text=0` does NOT mean no text was drawn: `Engine2D.draw_text` routes this lane
through the typed font backend (`engine.spl:1938` -> `backend_vulkan_font`),
touching no instrumented `VulkanBackend` entry point. **The census is blind to
text ops**, so any per-op cost attributed to opaque rects is an upper bound. The
frame is fully painted (`nonzero == pixel count`).

## Draw census (cold frame)

| counter | 900x760 | 300x253 |
|---|---|---|
| `rect_opaque` | 288 | 111 |
| `rect_alpha_blend` (each a full image composite) | 262 | 76 |
| of which **1x1** | **260** | **76** |
| `image` / `rect_masked` / `rect_list` | 2 / 0 / 0 | 0 / 0 / 0 |
| `text` reaching `VulkanBackend.draw_text` | 0 (see above) | 0 |

**41-47% of everything reaching the backend was a ONE-PIXEL image composite** —
anti-aliased rounded-corner pixels, each a staging acquire + host pack + upload
+ dispatch.

## Candidate fix, measured and held back

`_emu_corner_box_aa` was changed locally to gather a corner's partial-coverage
pixels into one `r x r` sprite and issue a single `draw_image_blend`:

| | 300x253 before -> after | 900x760 before -> after |
|---|---|---|
| cold ms | 68,426 -> **66,889** (-2.2%) | 1,095,789 -> **945,480** (-13.7%) |
| `rect_alpha_1x1` | 76 -> **0** | 260 -> **0** |
| `image_blend` | 76 -> **4** | 262 -> **14** |
| checksum | identical; page PPM **`cmp` clean** | **moved** (by 12,433,063) |

**The 900x760 divergence is NOT attributable to the coalescing**: that run also
carried a zero-area band guard, so two variables moved at once. `rect_opaque`
288 -> 286 at 900x760 but 111 -> 111 at 300x253 proves the guard was active only
in the diverging run, while the coalescing exercised the full Vulkan composite
kernel at 300x253 and was byte-identical there. Isolating it costs ~36 minutes.

**Nothing landed in product rendering code.** The coalescing is held pending that
isolated re-measurement; the guard was reverted (its benefit never manifested —
`cpu_fallback=false` in the BEFORE census with the zero-area dispatches present).
Only the read-only census landed.

Oracle: `test/02_integration/gpu/engine2d_rounded_rect_corner_batch_parity_spec.spl`
— 9/9 green on the unmodified tree, the coalesced tree, and after the revert.
Expected frames come from an INDEPENDENT re-derivation of the shared corner
coverage formula replayed through the per-pixel call shape (opaque / translucent
/ r = 3, 8, 20 / edge-straddling / clipped), plus three sabotage cases.

## Not measured, and why

- **Steady frames at 900x760, `overview.html`, 1920x1080**: a cold 900x760 frame
  is ~18 minutes here. The task's own rule excludes 1080p (cold >> 600 s).
- **Backend frame-scoped counters** (`dispatches_frame`, `submits`, `fences`,
  `font_atlas_*`, `present_*_count`): reset at a frame boundary before a probe can
  read them, so they are omitted rather than reported as zero.

## Measurement hygiene

The style engine prints `[rfm]`, `[font-inherit-trace]`, `[font-style-trace]`
UNCONDITIONALLY on the hot path — 815 `[rfm]` lines in the first 4,354 lines of
one cold log. Those files belong to another lane; the prints inflate every number
here and every cpu_simd number compared against.
