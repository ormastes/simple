# Retained damage replay rejects every backdrop-sampling (fluid_light) window

- **Id:** wm_retained_damage_rejects_parent_sampling_window_material_2026-11-26
- **Severity:** P2 — **Status:** fix-implemented-verification-pending

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

## Fix Implemented & Verification (2026-11-27)
- `src/os/compositor/engine2d_wm_frame_executor.spl`: added `_wm_batch_samples_parent`, `_wm_batch_glass_padding`, `_wm_expand_and_coalesce_rects`, `_wm_prune_non_parent_batch_for_rects`, and `_wm_replay_parent_sampling_composition`, wired into `Engine2dWmFrameExecutor.render` when `retained_plan.mode == DAMAGE_PLAN_LOCAL`. For parent-sampling glass compositions (`fluid_light`, `aetheric_dark`), replays non-parent backdrop batches onto an offscreen scratch `Engine2D` over causal-blur-padded `padded_rects` (`blur_radius` clamped to `[0, 4]`), replays intersecting parent-sampling batches cleanly on top, commits ONLY the unpadded `retained_plan.rects` back onto `self.engine`, and records `last_present_path = "software-retained-damage"`.
- CPU verification passed (`SIMPLE_ASSET_ROOT=C:\dev\simple`, `--mode=interpreter`):
  - `test/01_unit/os/compositor/wm_retained_parent_sampling_damage_spec.spl`: 4/4 passed (`fluid_light` clock tick, `aetheric_dark` clock tick, unfocused `fluid_light` glass content update, overlapping move over `aetheric_dark` glass — exact full-frame pixel parity).
  - `test/02_integration/rendering/engine2d_retained_group_opacity_damage_spec.spl`: 2/2 passed.
  - `test/01_unit/os/compositor/wm_retained_clock_tick_spec.spl`: 8/8 passed.
  - `test/01_unit/os/compositor/wm_retained_damage_behavior_spec.spl`: 8/8 passed.
- `test/02_integration/rendering/engine2d_wm_local_lane_clock_tick_spec.spl`: updated `fluid_light` and `aetheric_dark` expectations to `"software-retained-damage"`; passes 3/3 on Windows via `_vulkan_unavailable` fallback guard because `vkEnumeratePhysicalDevices(count=0)` returns `VK_ERROR_INITIALIZATION_FAILED (-3)`.
- `waiting-for:` Vulkan/GPU device verification of `test/02_integration/rendering/engine2d_wm_local_lane_clock_tick_spec.spl` on NVIDIA GB10 / llvmpipe (`SIMPLE_2D_REQUIRE_VULKAN=1`), as this Windows host lacks a Vulkan physical device.
