# Vulkan lane: the second full-surface readback is the BACKDROP BLUR, not the glass seed (2026-09-12)

Status: **FIXED.** `readbacks_per_frame` 2 -> 1 and `readback_bytes`
5,472,000 -> 2,736,000 on the audited configuration, with the page's pixels
byte-identical.

## F29's mechanism is wrong for this lane — do not chase the seed path again

`doc/08_tracking/bug/web_presenter_double_readback_and_host_paint_passthrough_2026-09-12.md`
attributed the extra readback to the parent-material "glass" seed at
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:2583` -> a device->host->device
pass-through through an offscreen delta surface.

**That branch never executes on this lane.** Measured on pristine `origin/main`
(`866825abefe`) with the gate's own configuration — `overview.html`, 900x760,
interpreter, `SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native
SIMPLE_VK_IMAGE_UPLOAD=u32 SIMPLE_VK_RECT_UPLOAD=u32` — **all 374 `[vk-order]`
lines in the frame carry `fb=3`**, a single framebuffer handle. The seed branch
creates a second Engine2D via `create_shared_vulkan_offscreen`, which would own
its own `d_framebuffer` and show a second handle in the trace. No second handle
appears, so no offscreen delta was ever created.

What the trace actually shows, twice (once per frame):

```
[vk-order] image-composite x=6 y=12 w=888 h=384 mode=1 rc=1 fb=3
[vk-order] host-fallback reason=blur-host-readback          <- added by this change
[vk-order] flush site=_flush_for_host_fallback ...
[vk-order] readback-entry ... fb=3                          <- the whole 900x760 surface
[vk-order] image-composite x=6 y=12 w=888 h=384 mode=0 rc=1 fb=3
```

The `reason=` line is the discriminating evidence and did not exist before: the
five `_flush_for_host_fallback` call sites in `backend_vulkan.spl` were
indistinguishable in the trace, and two of them (`blur-host-readback`,
`blend-mode-host-readback`) produce the same "readback then rect-sized copy"
signature. It is `draw_blur_rect`.

## Root cause

`VulkanBackend.draw_blur_rect` had no device implementation at all. It flushed
and delegated to `emu_draw_blur_rect` (`backend_emu_adv.spl:122`), which

1. `core.read_pixels()` — the **entire** framebuffer to the host (684,000 words
   at 900x760; 12x that at 4K),
2. box-blurs the rect with an interpreted scalar loop,
3. `core.draw_image(x, y, w, h, temp)` — uploads the rect back.

It was also **silent**: the flush it performs succeeds, so `mark_cpu_fallback`
was never reached and the audit reported `cpu_fallback_count=0` while a full
device->host->device round trip ran every frame.

## Fix

Two new compute kernels, both exact integer twins of their CPU references, both
pinned by the repo's regenerate-and-verify workflow:

* `src/lib/gc_async_mut/gpu/engine2d/shaders/blur_rect.comp` — twin of
  `emu_draw_blur_rect`. One 2D window, RAW sums, a SINGLE truncating division
  per channel, and 0 where the window holds no in-bounds sample. (The CPU
  reference is separable but keeps raw sums and counts in its intermediates, so
  it truncates once; an average-of-averages would differ by one ulp.)
  Generator `scripts/tool/gen-blur-rect-spirv.shs`, gate
  `scripts/check/check-blur-rect-spirv-pinned.shs`.
* `src/lib/gc_async_mut/gpu/engine2d/shaders/glass_material.comp` — twin of
  `engine2d_draw_ir_glass_material_pixels`, including the box blur's DOUBLE
  truncation (each row average is packed to 8 bits before the vertical pass),
  the saturation matrix, rounded-corner test, surface tint and vertical
  gradient. Generator `scripts/tool/gen-glass-material-spirv.shs`, gate
  `scripts/check/check-glass-material-spirv-pinned.shs`. This closes the
  `device-glass-dispatch-not-supported` gap on the Draw IR canonical glass path
  that Metal already had — a different route from the one this page takes, but
  the same host round trip.

Both dispatch through one new helper,
`vulkan_dispatch_region_kernel_checked` (`backend_vulkan_helpers.spl`). It is
deliberately NOT `vulkan_dispatch_image_composite_checked`: that one OWNS its
binding-1 buffer and frees it on every exit, which is correct for a one-shot
upload and fatal here, since the output buffer must survive to be blitted back.

The copy-back reuses `_finish_image_composite`, so it is byte-for-byte what
`draw_image(x, y, w, h, pixels)` already did — same clip, same damage and dirty
bookkeeping — with the pixels already on the device. The kernel's output buffer
is a single `_acquire_image_source` allocation serving both roles, so the pool
owns its lifetime exactly as for an ordinary image upload.

Fail-closed everywhere: any decline leaves the framebuffer untouched, the host
twin still paints, and the round trip is now **recorded** —
`mark_cpu_fallback("glass-device-unavailable")`. The pipelines are optional on
the session (`glass_error` / `blur_error`), mirroring the batched-rect lane: a
driver that cannot build them degrades in throughput, never in pixels.

## Evidence

Binary `/Users/ormastes/simple/build/cargo-r2/release/simple`
(`39528776 1789199850`, bracketed identical after every run), macOS/MoltenVK,
one run at a time, env as above.

Gate `scripts/check/check-web-vulkan-gpu-boundary-audit.shs`, `overview.html`,
900x760, 2 frames:

| key | before | after |
|---|---|---|
| `readbacks_per_frame` | 2 | **1** |
| `readback_bytes` | 5,472,000 | **2,736,000** |
| `uploads_per_frame` | 25 | 24 |
| `submits_per_frame` | 17 | 17 |
| `host_pixel_iterations` | 16 | 16 |
| `cpu_fallback_count` | 0 | 0 |

Verdict before and after is still `FAIL`, honestly: the two remaining
violations, `host_pixel_iterations=16 (font_atlas_pack_u32_to_u8)` and
`submits_per_frame=17`, belong to the font-atlas lane and the submission
batching, neither of which this change touches.

**Pixel oracle.** A full-page FNV-1a digest of every rendered word, both frames,
pristine vs. changed tree, same binary:
`-3650045829680336039` before and `-3650045829680336039` after — the page is
byte-identical. Sampled pixels across the glass rect likewise unchanged.

Spec: `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_device_glass_blur_spec.spl`
— 7/7 on a real Vulkan device. It proves device-vs-CPU byte equality for the
blur (the reproducing spec), pixels outside the rect untouched, the degenerate
radius declined exactly as the host twin declines it, device-vs-host byte
equality for the glass material (the generalization spec, adjacent code path),
and **zero framebuffer readbacks during the glass pass**.

## Pre-existing reds, re-checked on pristine `origin/main`

Both are unrelated to these files and unchanged by this branch:

* `backend_vulkan_image_exact_scratch_spec.spl` — 3/6 passing (F31 recorded
  5/6; it has degraded further on `main` since, independently of this lane).
* `vulkan_resident_2d_spec.spl` — 4/11 passing.

Not fixed here: neither is caused by `draw_blur_rect`, the glass material, or
the blit pipeline, and repairing them is well beyond a 30-line change.

## Still open, recorded rather than half-done

The `image-composite x=6 y=12 w=888 h=384 mode=1` that precedes the blur is a
340,992-pixel image uploaded from the host each frame — the *other* half of
"the GPU is used as a pass-through" that the metrics doc ranked as defect #4. It
is a different producer from the blur and is untouched here.

## Test-tree divergence step-over (recorded, as the guard requires)

`sh scripts/check/check-test-tree-divergence-delta.shs origin/main <tip>` ->
`PASS — 3209 pre-existing offender(s), 0 introduced by this range` (exit 0).
The base itself is red (`3943 diverged vs 965 baselined; 26 mirror-only`), left
by other lanes; this range introduces none of it and touches no mirrored test
path. Offender list saved by the helper at
`$TMPDIR/test_tree_divergence_preexisting.txt`.

## Why `submits_per_frame` is still 17, and what it would take

The readback half of this defect is closed; the submit half is NOT, and is
deliberately left rather than half-done.

Measured before and after: **17 submits per frame, unchanged.** The blur is
submit-neutral, not submit-free. The host path already cost one submit (the
`_flush_for_host_fallback` before the readback); the device path spends the same
one, because the kernel must READ framebuffer content that earlier batched
dispatches produced, and the only barrier available at this seam is a queue
submission. The copy-back is already batched (`_finish_image_composite` ->
`_enqueue_image_composite`), so it adds nothing. The remaining ~16 submits have
other producers — the frame runs 107 dispatches — and none of them is the blur.

Reaching `submits_per_frame=1` needs the batching machinery to accept a
two-storage-buffer kernel and an intra-command-buffer barrier between the
producer dispatches and the kernel that samples their output.
`_enqueue_image_composite` is shaped for the single-source image-composite
pipeline only. That is a change to the frame batcher, not to this kernel, and
is not attempted here.

**One correction for anyone picking that up:** do not implement the blur as a
"separable box blur x3". The CPU reference (`emu_draw_blur_rect`) is a SINGLE
box pass that keeps raw sums and divides once. A triple separable pass is a
different filter and would break the byte-identical pixel result this change
currently achieves.
