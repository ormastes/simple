# Retained damage replay rejects every scene with an unfocused (opacity 930) window

- Status: open (P2), found 2026-11-26 on this Linux aarch64 host (GB10 and
  llvmpipe), seed `cargo-target-wr-seed1126b`.
- File: `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`, the
  embedding loop in `_engine2d_draw_ir_render_composition_damaged_with_images`
  (~line 5018) and the single-root fast path (~line 5279).

The damaged executor refuses any batch with `opacity_milli != 1000`
(`retained-composition-unsafe-embedding`). The shared WM scene gives every
unfocused window batch opacity 930, so a hosted frame with any unfocused
window falls back to a full repaint at `compositor_engine2d.spl:1099` and
`engine2d_wm_frame_executor.spl:440`. This is independent of the theme: the
plain (no package) stream carries the same 930 batch.

Probe (one window at 10,36 120x80, `focused=false`): batches
`wm-desktop`, `wm-chrome`, `wm-taskbar-objects` at op 1000, `surf` at op 930
clip true, for both the plain stream and fluid_light.

Fix direction: replay a group-opacity embedding under the damage clip by
compositing the whole group (group surface or full-group redraw inside the
clip), then prove device == CPU against split full frames, as
`engine2d_themed_wm_fresh_device_spec.spl` does for translucent root rects.

## Fix (2026-11-26)
The retained replay layers a sub-opaque embedded surface through the same
predicate as the full frame (`_engine2d_draw_ir_uses_embedded_surface`) and
the same layer pool off Vulkan. It therefore layers it the same way the
full frame does (`_engine2d_draw_ir_retained_layer_batch`). It renders one
surface-sized layer per batch per replay, holding only the commands that
touch the union of that batch's damage clips. It then composites that layer
at `opacity_milli` under each damage clip.

Evidence: `engine2d_retained_group_opacity_damage_spec` passes 2/2 on NVIDIA
GB10 and on llvmpipe, under the fluid_light and aetheric_dark themes. The
damage rect crosses the window edge. The replay equals the device's first
frame outside the damage and a fresh device frame inside it. A fresh full
device readback, with a poisoned canary pixel, agrees.

Perf on GB10, seed fb80903917d6d5f5, 3 rounds: a full frame took
11.3-16.2 s, replay1 11.1-11.2 s and replay3 11.6 s. The replay is exact but
gives no speedup, because the layer's offscreen create and readback cost
about as much as the full frame. Any replay touching a window costs about a
full frame on Vulkan.

Still rejected:
- the prepared-plan site;
- the single-root path;
- parent-sampling batches (tracked as
  `wm_retained_damage_rejects_parent_sampling_window_material_2026-11-26`).
