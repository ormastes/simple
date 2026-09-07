# GPU glyph rasterization is NOT-STARTED on Vulkan and Metal; deferred for want of a device

Date: 2026-09-06
Status: DEFERRED (no device on the reference host)
Area: lib / gc_async_mut / gpu / engine2d — font offload

All `file:line` below were read at `origin/main` `461e48379ff` (2026-09-06).
Re-anchor by symbol before trusting a line number on a later tip.

## Symptom

Neither the Vulkan nor the Metal 2D backend rasterizes glyphs on the GPU. Both
rasterize on the CPU and then move already-lit pixels to the device:

| backend | what actually happens | file:line |
|---|---|---|
| Vulkan, bitmap default font | `text_blit_buffer` CPU raster, then `draw_image_blend` | `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl` `me draw_text` / `me draw_text_bg` |
| Metal, hi-res text | host `_hires_glyph_coverage` raster, then blit | `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl` `me draw_text_hires` |
| both, atlas lane | atlas **lookup + composite**, not rasterization | `src/lib/common/gpu/font_atlas_composite.spl` `font_atlas_subrect_pixels` |

**The atlas blit is a lookup, not a raster.** `kernel_glyph_atlas_blit`
(`backend_metal.spl:708`, `:1914`) samples an atlas the host already filled and
composites coverage; it computes no outline, no coverage, no scan conversion.
Conflating the two is the recurring reading error this record exists to stop —
"Metal blits glyphs on the GPU" is true and is *not* "Metal rasterizes glyphs on
the GPU".

## What already exists, so the gap is narrower than "no GPU glyph work"

- **Bitmap glyph raster on the generated-kernel lane is real and present** for
  three providers: `cuda_session.spl:394`, `opencl_session.spl:417`,
  `rocm_session.spl:242`, each `me bitmap_glyph_raster_kernel(width, height,
  args_ptr)`. That is a genuine GPU rasterizer for the 5x7 bitmap font.
- **Metal blits bitmap glyphs on-GPU** through the atlas kernel above.
- **Vulkan's font-atlas composite lane is real** (`backend_vulkan_font.spl`,
  fenced dispatch), and `Engine2D.draw_text` already routes TTF/vector text into
  it (`engine.spl` `me draw_text` -> `draw_text_configured` ->
  `_draw_font_batch_staged` -> `_draw_font_batch_plan`). PR #422 (OPEN as of
  2026-09-06) adds the bitmap 5x7 path to that same lane.

The missing piece is therefore specifically: **a GPU *vector* (outline ->
coverage) rasterizer for Vulkan and Metal.** Nothing else.

## Why it is deferred rather than built

1. **No GPU device on this host.** A rasterizer is a pixel-correctness claim;
   every device-free proof available here (word-layout parity, frame-contract
   predicates, CPU twins) pins the *plumbing*, never a rasterized pixel. Building
   one and shipping it green from device-free specs would manufacture exactly the
   class of false evidence PR #410 was opened to remove.
2. **No Metal device evidence exists on this machine at all** — see the DirectX
   record's sibling note and the wiki entry; `build/test-macos-metal-render-log-pass/capture.env`
   is a hand-written fixture (literal `macos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE`,
   with `-fail`, `-bad-capture-magic`, `-missing-inputs` sibling fixture dirs),
   and `doc/08_tracking/test/test_result.md` records both Metal perf specs as
   `unknown`, never a pass.
3. The narrower verifiable step (bitmap text -> existing Vulkan atlas lane) was
   taken instead, in PR #422.

The existing `# TODO: [gpu]` markers for this gap **stay TODOs**. Deferred is not
done; do not convert them to NOTE (`.claude/rules/code-style.md`).

## Closing evidence (what flips Status)

A real GPU device that rasterizes glyphs, with a captured trace:

- a Vulkan or Metal host that executes an outline -> coverage kernel, and
- a captured frame trace from that device (RenderDoc `.rdc` / Xcode `.gputrace`
  produced by the tool, **not** a hand-written `capture.env`), and
- readback whose provenance is `device_readback` — not `cpu_fallback`,
  `host_cache_after_device_copy`, `completion_unknown` or `readback_failed`
  (`backend_vulkan.spl:1468-1519` emits all five literals), and
- a pixel diff against the CPU rasterizer for the same face/size, recorded.

Anything short of all four leaves this record OPEN.
