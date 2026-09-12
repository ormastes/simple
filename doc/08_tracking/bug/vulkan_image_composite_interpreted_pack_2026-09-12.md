# Vulkan image composites pack `[u32]` to `[u8]` in interpreted Simple

Date: 2026-09-12. Status: **OPEN — fix landed opt-in, numbers below.**
Lane: `SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native
SIMPLE_2D_BACKEND_STRICT=1 SIMPLE_EXECUTION_MODE=interpreter`, binary
`/Users/ormastes/simple/build/cargo-r2/release/simple`
(`stat -f '%z %m'` = `39368072 1789171430`, bracketed identical every run).
Page: the composed `css-layout` catalog page, 40,960 bytes.

## The defect

`_draw_image_composite_native_impl` (`backend_vulkan.spl`) receives the image as
`[u32]` and handed it to `vulkan_sffi_copy_to_buffer_prefix`, whose byte
marshaller masks each element to ONE byte. So `_prepare_image_upload`
(`backend_vulkan_helpers.spl:226`) exploded every pixel into four interpreted
array stores by hand:

```
self.image_upload_scratch[offset]     = _u32_to_u8(pixel & 0xFF)
self.image_upload_scratch[offset + 1] = _u32_to_u8((pixel >> 8) & 0xFF)
...
```

That is `4 * pixel_count` interpreted stores per composite — **2.7 million for
one 900x760 full-surface image**. It is the same defect class F8 fixed for
readback and R2 for rect uploads (census class R10), and the per-op attribution
run measured `image_composite` at **544,646 ms of a 789,177 ms frame (69%)**.

## Why it is the image path's turn, and why the fix is smaller here

The rect lane's typed upload still PACKS — it builds a `[u32]` words array from
separate `rects`/`colors` arrays. The image lane packs **nothing**: `pixels` is
already `[u32]`, so the typed branch is one call,

```
upload_ok = vulkan_sffi_copy_to_buffer_u32(d_src, pixels, 0)
```

and the runtime performs the identical little-endian widening the loop above
did by hand. Opt-in via `SIMPLE_VK_IMAGE_UPLOAD=u32`, default OFF for the same
reason as `SIMPLE_VK_RECT_UPLOAD`: the interpreter's unknown-extern path aborts
the whole process on a binary predating `rt_vulkan_copy_to_buffer_u32`, before
any in-tree guard could decline. See
`typed_vulkan_upload_no_fallback_on_old_binary_2026-09-11.md`. Confirmed present
in the measured binary: `strings | grep -c rt_vulkan_copy_to_buffer_u32` = 9.

## Instrumentation added (level-gated, `SIMPLE_VK_TIMING=1`)

Four buckets — `image_pack_u32_to_u8`, `image_source_alloc`,
`image_descriptor_dispatch`, `image_exact_size_byte_fallback` — plus
`image_composite_stats`, which tallies each composite as full-surface (source
>= 90% of the destination surface) or small WITH its wall time, and counts the
exit taken at each of the ten `return 0` guards. That last counter exists
because every one of those exits drops the caller to `emu_draw_image_*`, a full
host readback plus software blend; until it existed the 544 s could not be split
between "the pack is slow" and "the device path declined", which need opposite
fixes.

## Measured

Both sides carry the instrumentation; the "before" is the flag OFF, not the
pre-instrumentation tip. See the metrics doc for the full table.

## Origin of the full-surface composites

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl:597`
— `present_layout_pixels_with_engine2d_readback`, the "default (upload-bound)
present path". For any non-CPU backend it acquires an engine, `clear(base)`,
then `engine.draw_image(0, 0, width, height, pixels)` with a **host-rasterized
full layout surface**, and immediately `read_pixels_with_source()`. The GPU is a
pass-through: upload the whole page, read the whole page back.

Two further full-surface producers exist and are NOT the Vulkan lane's:
- `draw_ir_adv.spl:3255` — `engine.draw_image(0, 0, eng.width(), eng.height(),
  eng.read_pixels())` IS an identity blit of the surface onto itself, but it is
  explicitly gated to `cpu`/`cpu_simd`/`software` (`host_memory_writeback`), a
  workaround for interpreter deep-copy-on-assign. Device backends skip it.
- `draw_ir_adv.spl:2600` — the parent-material offscreen seed, a readback of the
  parent region blitted into a child engine.

**Not eliminable as an identity blit.** The presenter's source is HOST pixels
the CPU rasterizer produced, not a device surface, so there is nothing already
on the device to composite from. Eliminating it means not rasterizing on the
host at all — a different and much larger change than this one. What the typed
upload does is make the unavoidable transfer cost a runtime memcpy instead of
2.7M interpreter steps.

## Cache: not implemented, and why

The task asked for a cache keyed on `(pixels identity/digest, w, h)`. It is not
implemented, deliberately:

1. **No sound O(1) key exists in this tree.** There is no array-identity
   primitive, and the producer supplies no generation the way
   `FontRenderBatch.atlas_generation` does for the font atlas.
2. **An interpreted digest is the same cost class as the pack it would avoid.**
   `font_atlas_payload_sha256` measures **8.3 s** walking a 1M-element atlas for
   exactly this purpose. Hashing 684k pixels to avoid packing 684k pixels is not
   a saving.
3. **A cache would pin a pooled device slot.** `_acquire_image_source` /
   `_release_image_source` run a 256-slot pool that already exhausts mid-frame
   at 264 composites and flushes to recover; holding slots across frames makes
   that worse.

A sound version needs a producer-side key plumbed through the public
`draw_image` API. Filed here rather than approximated with a sampled digest,
which would silently paint wrong pixels on a false hit.

## Guard against regression

`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_image_typed_upload_spec.spl`
— device-requiring (fails, never skips), 4x4 per-pixel-distinct oracle at a
known offset, an outside-the-edge check, 1x1 and full-surface payloads, two
composites in painter order, and `vulkan_image_upload_evidence()` asserting
which lane actually ran. That last one is load-bearing: the two lanes produce
identical device bytes by construction, so no pixel can witness the difference
and a perf A/B could otherwise measure the byte path twice.
