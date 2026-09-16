# Engine2D Vulkan `pixels: [u32]` upload is SLOWER than CPU compositing (measured 1.56x)

**Filed:** 2026-09-11 · **Status:** open · **Area:** ui / engine2d / gpu
**Host:** Apple M4, macOS arm64. Binary `bin/release/aarch64-apple-darwin-macho/simple`,
size 26264696, mtime 1788766698, `SIMPLE_EXECUTION_MODE=interpreter`.

## Measurement

Same program, same frames, same tree, one binary — only `SIMPLE_2D_BACKEND` toggled. Eight
identical 320x180 stub frames composited per backend through
`Engine2D.create_with_backend_fast` -> `clear` -> `draw_image(pixels: [u32])` -> `present`
-> `read_pixels`, then written as P6 PPM.

| backend requested | backend reported | tabs | wall_ms_total |
|---|---|---|---|
| `cpu_simd` | `cpu_simd` | 8 | **14691** |
| `vulkan`   | `vulkan`   | 8 | **22851** |

Vulkan is **1.56x slower**, i.e. +8160 ms over 8 frames (~+1020 ms/frame at 57,600 px).

Receipts (both carry binary identity, backend requested/reported and per-tab `wall_ms`):
`build/chrome-showcase/cpu_simd/receipt.env`, `build/chrome-showcase/vulkan/receipt.env`.
Aggregate: `sh scripts/check/check-chrome-web-showcase-perf.shs` ->
`chrome_web_showcase_ms_per_px=0.040830`.

`engine2d_backend_reported=vulkan` is the real device path, not a software fallback — a
fallback would have reported `vulkan-poisoned-software` (`engine.spl:433`).

## Why this is a real finding and not just "GPU has fixed overhead"

It is partly fixed overhead, and the frames here are small. But the shape is what matters:
the **v1 CPU round trip is the whole cost model**. Every frame goes host -> GPU as a
`[u32]` upload and GPU -> host again through `read_pixels`, so the GPU does a trivial blit
between two full-frame PCIe/unified-memory copies. Nothing in that path gets cheaper at 4K;
it gets 72x more expensive per frame, in exactly the direction this measurement points.

This is the cost the deferred zero-copy row was written to remove: blocked row **B5** of
`doc/03_plan/ui/chrome_dynlib/chrome_dynlib_vulkan_showcase_plan.md` — "Engine2D has no
external-memory import; needs new `rt_*` surface + `VK_EXT_external_memory_dma_buf`
(Linux) / MoltenVK IOSurface (macOS)", explicitly out of scope for S1-S3. This record is
the measured evidence that B5 is a performance requirement and not only an elegance one.

## Not yet established

- Whether the gap is upload, readback, or per-frame command submission — not profiled.
  Split it before optimising; the plan's own text assumes upload, and that is an assumption.
- Whether it holds at 4K (3840x2160). Only 320x180 was measured. Re-measure before quoting
  a ratio at any other size.
- Whether the interpreter's own per-call overhead inflates the Vulkan side more than the
  CPU side. Both ran interpreted, so the comparison is fair, but the absolute numbers are
  not native-build numbers.

## Resume

1. Split the per-frame cost (upload / blit / readback / submit) with counters on both
   backends at 320x180 and 3840x2160.
2. If upload+readback dominates, that is B5: file the external-memory import lane and cite
   this record.
3. Re-run `sh scripts/check/check-chrome-web-showcase-perf.shs` after any change; it prints
   `chrome_web_showcase_backend_<name>_wall_ms_total` per backend and is the regression
   surface for this row.
