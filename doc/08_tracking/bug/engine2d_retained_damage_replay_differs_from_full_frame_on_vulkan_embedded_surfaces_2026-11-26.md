# Retained damage replay differs from the full frame on Vulkan embedded surfaces

- **Id:** engine2d_retained_damage_replay_differs_from_full_frame_on_vulkan_embedded_surfaces_2026-11-26
- **Severity:** P2

## Symptom
On Vulkan, `_engine2d_draw_ir_render_batch_embedded` renders every embedded
surface batch through its own offscreen layer and composites it with
`draw_ir_composite_readback`. That includes opaque, clipped WM window chrome
(`needs_real_offscreen` is true for vulkan). The retained damage replay
(`_engine2d_draw_ir_render_composition_damaged_with_images`) drew the same
batch straight onto the parent under the damage clip. Translucent pixels,
such as the window shadow, then round differently.

## Repro (hosted local lane, before the fix)
Use `test/02_integration/rendering/engine2d_wm_local_lane_clock_tick_spec.spl`
in its default-chrome example: a 160x120 scene with a focused 140x84 window
at (10,36) and a clock tick 09:41 -> 09:42. Do a forced full device readback
of the replayed frame and compare it with a fresh Vulkan executor frame of
09:42. 240 px differ at x 150..154, y >= 72 (the window's right edge, inside
the tile-aligned plan rect), for example 4280638921 vs 4280639178, which is
1 LSB in two channels. This shows on NVIDIA GB10 and on llvmpipe.

## Fix
`_engine2d_draw_ir_uses_embedded_surface(batch, eng, depth)` is now the only
rule deciding whether a batch is layered. Both the full frame and the
replay call it. The replay wrapper `_engine2d_draw_ir_retained_layer_batch`
excludes only CSS opacity groups, which restore with their own rule, and
Metal, which can't be proven on this host.

The replay now runs batch-major. That paints the same pixels as
damage-major, because `_engine2d_draw_ir_damage_rects_valid` guarantees the
damage rects are pairwise disjoint. Each layered batch is rendered once,
over the union of its damage clips, into a layer acquired exactly as the
full frame acquires it:
- off Vulkan, the single-slot `_engine2d_embed_offscreen_acquire` pool,
  which the non-reclaiming SimpleOS bump heap needs;
- on Vulkan, a fresh device offscreen that is shut down after use.

The layer is then composited under each clip.

## Perf
Any replay that touches a window now costs about a full frame on Vulkan.
The layer's offscreen create, render and readback dominate:
- a clock tick with the window under the clock: 5.68-5.72 s, against
  5.72-5.78 s for a full frame;
- a 930 content replay: about 11.1-11.6 s, against 11.3-16.2 s.

Replays that miss every window stay cheap: a clock tick drops from 5.45 s
to 53 ms.
