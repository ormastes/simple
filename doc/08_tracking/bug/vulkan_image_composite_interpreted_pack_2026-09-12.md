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

## Measured, 900x760, flag OFF (both sides carry the instrumentation; the
"before" is the flag OFF, not the pre-instrumentation tip)

| bucket | n | total ms | max ms |
|---|---|---|---|
| frame | | **830,186** | |
| image_composite | 264 | 573,780 | 185,586 |
| **image_pack_u32_to_u8** | 264 | **391,259** | 99,721 |
| **image_exact_size_byte_fallback** | 262 | **180,995** | 92,529 |
| image_source_alloc | 264 | 315 | 4 |
| image_descriptor_dispatch | 264 | 94 | 2 |
| sffi_upload | 264 | 907 | 669 |

`image_composite_stats full_surface=4 full_surface_ms=563,638 small=260
small_ms=10,148 max_px=12,874,224 reasons: ok=264`.

**Three things this settles that the earlier attribution could not.**

1. **`reasons: ok=264` — the device path ran EVERY time.** Not one composite
   took any of the ten `return 0` exits, so none fell back to
   `emu_draw_image_*`. The metrics doc's alternative hypothesis (a silent host
   readback via the fallback that never calls `mark_cpu_fallback`) is
   **excluded**. The cost is host packing, as suspected.
2. **The composite is host-bound by three orders of magnitude.** Device
   allocation 315 ms, descriptor+dispatch 94 ms and the SFFI upload 907 ms sum
   to 1.3 s against 572 s of packing. There is no device-side term to optimise.
3. **Every composite packs the image TWICE, not once** — a second, independent
   defect this run found. `image_exact_size_byte_fallback` fired **262 of 264**
   times, at 181 s. Cause, at `sffi_vulkan.spl:1279`
   (`vulkan_sffi_copy_to_buffer_prefix`): on the interpreter array ABI the
   prefix upload is admitted **only when `byte_count == data.len()`** and fails
   closed otherwise. `image_upload_scratch` is grown to a high-water mark and
   never shrunk, so after the first large image every smaller composite has
   `byte_count < scratch.len()`, the prefix declines, and
   `_pixels_to_bytes(pixels, pixel_count)` packs the whole image a second time.
   The scratch reuse optimisation therefore *causes* a full extra pack on all
   but the first two composites. The typed lane bypasses both packs; the byte
   path's double pack remains and is filed here rather than patched, because
   the right fix (shrink-to-fit, or an exact-size scratch) is a separate change
   with its own oracle.

**`max_px = 12,874,224`.** The largest composite's SOURCE is 12.87M pixels —
**18.8x the 684,000-pixel destination surface**, i.e. a very large image scaled
down, not a surface-sized layer. That single composite accounts for the
`image_composite` max of 185,586 ms (99.7 s pack + 92.5 s byte fallback). Note
also that the `full_surface=4` tally classifies "source >= 90% of THIS engine's
surface", so a small offscreen child engine at `draw_ir_adv.spl:2600` counts as
full-surface too; read `max_px` alongside the count, never the count alone.

## Measured, 900x760, flag ON (`SIMPLE_VK_IMAGE_UPLOAD=u32`)

| bucket | n | before ms | after ms |
|---|---|---|---|
| **frame** | | **830,186** | **259,523 (-68.7%)** |
| image_composite | 264 | 573,780 | **940** |
| image_pack_u32_to_u8 | 264 | 391,259 | **0 (bucket never fires)** |
| image_exact_size_byte_fallback | 262 | 180,995 | **0 (bucket never fires)** |
| image_blend | 262 | 287,818 | 594 |
| rect | 550 | 288,153 | 909 |
| image_source_alloc | 264 | 315 | 332 |
| image_descriptor_dispatch | 264 | 94 | 93 |
| font_composite | 23 | 68,745 | 70,708 |

`image_composite_stats ... upload_mode=u32 upload_reason=typed-requested
reasons: ok=264`.

**The typed lane genuinely ran.** `upload_reason=typed-requested` is the load
bearing check: the two lanes write identical device bytes by construction, so a
`typed-declined` here would mean the run measured the byte path twice and the
speedup would have to be attributed to something else.

**Target MET.** cpu_simd on this page at 900x760 is 263,636 ms; the Vulkan lane
is now **259,523 ms**, i.e. under the bar for the first time, from 830,186 ms.
The image composite went 573,780 -> 940 ms, a 610x reduction, because both
interpreted packs disappear: the typed branch returns before
`_prepare_image_upload` is ever called, so neither pack bucket fires at all.

Note `rect` also fell 288,153 -> 909 ms. That is not a second fix: `rect` and
`image_blend` are outer buckets that WRAP the composite, so they were carrying
its cost.

**Correctness: PPM byte-identical at 900x760**, `cmp` clean over all 2,052,015
bytes, frame checksum `8316162126305609402` on both sides. This is worth
stating precisely because
`web_catalog_900x760_frame_checksum_nondeterministic_2026-09-12.md` (F16)
records that this page renders non-deterministically at this size: the oracle
was therefore not ASSUMED to hold, it was measured, and on this pair it did.
A future run that differs is F16's nondeterminism, not evidence against this
change -- use the differ, and the 300x253 pair, to tell them apart.

**What is now dominant.** `font_composite` at 70,708 ms is 27% of the remaining
frame and is the next term, not the image path.

## Measured, 300x253 — no improvement, and that is the prediction

| | before | after |
|---|---|---|
| frame | 30,861 ms | 33,403 ms |
| image_composite_stats | `full_surface=0 small=76 max_px=1` | same |
| image_pack_u32_to_u8 | 2 ms | bucket never fires |

All 76 composites at this size are **1x1**, so there is nothing to pack: the
pack bucket reads 2 ms before the change. The difference between the two runs
is run-to-run noise on a shared machine, not a regression attributable to the
flag, and it is reported rather than smoothed. This size is the control that
shows the win at 900x760 comes from the large-image population specifically.

**PPM byte-identical at 300x253** (`cmp` clean, checksum
`-6077680819631676143` on both sides). This is the oracle the task asked for at
this size, and unlike the 900x760 pair it is on a size F16 does not record as
non-deterministic.

## Sabotage: the oracle discriminates

Byte-swapping each word in the typed branch before handing it to
`vulkan_sffi_copy_to_buffer_u32`, then running the spec with
`SIMPLE_VK_IMAGE_UPLOAD=u32`:

```
x places every source pixel at its own destination ... expected 16 to equal 0
x composites a single-pixel image ... expected 406354175 to equal 4286068760
x composites a FULL-SURFACE image ... expected 4096 to equal 0
x paints two composites in one frame in painter order ... expected 32 to equal 0
7 examples, 4 failures
```

Every pixel of every payload mismatches. Reverted, the same command reports
`7 examples, 0 failures`, and the DEFAULT byte path reports `7 examples, 0
failures` as well -- the byte-fallback equivalence the task asked for.

Two examples correctly stayed GREEN under sabotage, and both are meant to: the
outside-the-edge check only inspects untouched ground pixels, and the evidence
example asserts WHICH LANE ran, not what it wrote. An oracle that went red on
all seven would have been testing less precisely, not more.

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
