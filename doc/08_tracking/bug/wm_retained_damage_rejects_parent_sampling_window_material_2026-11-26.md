# Retained damage replay rejects every backdrop-sampling (fluid_light) window

- **Id:** wm_retained_damage_rejects_parent_sampling_window_material_2026-11-26
- **Severity:** P2 — **Status:** open

## Symptom
On the hosted local lane the composition targets the CPU. Under fluid_light,
the production default theme, the window chrome batch (`surf`) samples its
parent backdrop. `_engine2d_draw_ir_render_composition_damaged_with_images`
rejects any batch that samples its parent with
`retained-composition-unsafe-embedding`.

So with fluid_light, every clock tick or window move in a scene that has a
window repaints the whole frame. The clock-tick replay
(`wm_local_lane_clock_tick_full_repaint_2026-11-26`) reaches only the
default chrome.

## Repro
`test/02_integration/rendering/engine2d_wm_local_lane_clock_tick_spec.spl`,
example "fails closed to a full device frame when the fluid_light window
samples its backdrop". The tick presents `path=software`. The pixels still
equal a fresh frame, so the fallback is correct, just slow.

## Why it is not a one-line admit
Re-running the material under the damage clip is wrong. Outside the clip
the framebuffer holds the window's own composited output, not the backdrop,
and the blur kernel samples across the clip edge. A fix has to re-render the
backdrop for the clip padded by the material radius, then run the material.
