# Engine2D Vulkan readback returns 0 pixels at >= 7680x4320 in the showcase scene

Filed 2026-09-03. Status: OPEN, scene-dependent — see the contradiction below,
which is the most useful part of this record.

## Symptom

`src/app/ui_showcase/hosts/main_primitive_showcase.spl` on the **vulkan**
backend at 7680x4320 returns **0 pixels** with `src=completion_unknown`, with
and without the documented no-clear workaround. `readback_us=1141` — an
instant bail rather than a slow path, so the readback is refused up front, not
attempted and failed. Fine at <= 2880x1864.

## The contradiction, which narrows it

`test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl` on the SAME backend, SAME binary and SAME
7680x4320 framebuffer reads back **successfully** — measured repeatedly, e.g.
`readback_us=624490` over 8 frames with correct pixel content, and the
Simple-vs-C bit-diff gate passes.

So this is NOT a blanket "readback breaks above 4K" limit. The two scenes
differ in WHAT they draw:

- `vk2d_bench.spl` draws only `clear` + 64 `draw_rect_filled` — all GPU-native.
- `main_primitive_showcase.spl` draws all 30 primitives, which includes the
  **forced-readback tier** (`draw_rect_blend`, `draw_blur_rect`,
  `draw_rect_blend_mode`, `draw_image_blend`, `draw_image_scaled_blend`) and
  the 16 `emu_*` primitives that emit large dispatch backlogs.

`completion_unknown` is set when a dispatch or flush fails, so the likely
mechanism is a failed/oversized intermediate operation in one of those tiers at
33.2 Mpx, latching the backend into the unknown-completion state — after which
readback correctly refuses rather than returning wrong pixels.

That makes the refusal itself sound behaviour; the defect is whatever fails
upstream.

## Where to look first

1. The forced-readback tier's host round trip at 33.2 Mpx (132.7 MB): a
   staging/transfer size limit would fire exactly here and nowhere below 4K.
2. `maxStorageBufferRange` is never queried — spec floor is 128 MiB and this
   framebuffer is 132.7 MB, i.e. **just over** the floor at 8K screen and 2x it
   at 8192x8192. See
   `doc/08_tracking/bug/engine2d_8k_default_sizing_inventory_2026-09-03.md`.
3. The damage-row cap (16,384) admits only 2-3 full-height rects at these
   heights, forcing a full-frame path.

## Reproduce

```sh
cd /private/tmp/simple-vkbench
E="DYLD_FALLBACK_LIBRARY_PATH=/opt/homebrew/lib SIMPLE_RUST_SEED_WARNING=0 SIMPLE_LIB=src \
VK_ICD_FILENAMES=/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json"
B=src/compiler_rust/target/vulkan/release/simple
env $E VK2D_BACKEND=vulkan SHOWCASE_MODE=virtual SHOWCASE_W=7680 SHOWCASE_H=4320 \
  $B run src/app/ui_showcase/hosts/main_primitive_showcase.spl     # 0 pixels
env $E VK2D_W=7680 VK2D_H=4320 VK2D_RECTS=64 VK2D_FRAMES=8 \
  $B run test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl                          # succeeds
```

Related: `doc/08_tracking/bug/vulkan_engine2d_sequential_frames_flaky_moltenvk_2026-09-02.md`.
