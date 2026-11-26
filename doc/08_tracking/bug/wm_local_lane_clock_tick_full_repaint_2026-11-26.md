# Hosted local WM lane repaints the full frame on every clock tick

- **Id:** wm_local_lane_clock_tick_full_repaint_2026-11-26
- **Severity:** P2 — **Status:** verified (2026-11-26, Linux aarch64, NVIDIA GB10 + llvmpipe)

## Symptom
`Engine2dWmFrameExecutor.retained_scene_damage_plan` returned a FULL damage
plan whenever `clock_label` changed. A clock tick is the most frequent
taskbar change, so the retained damage replay never ran for it on the
hosted local lane.

## Fix
`engine2d_wm_clock_rect(composition)` returns a padded box for every clock
text in the composition: `taskbar-clock`, and `taskbar-tray-label-clock`
from the production tray item. The executor records those boxes, plus a
clock-independent taskbar layout key (`engine2d_wm_taskbar_layout_key`:
pinned, running, and tray with the clock label blanked), with each
presented frame.

`simpleos_runtime_taskbar_revision` still mixes the clock in. That stays
as-is, because the shell `need_render` gate, input handling, the
rv64/arm64 producers and the ssh entry all use the revision as their
repaint trigger, and they can't be tested from here.

The rule is:
- If the revision changes, the layout key is unchanged and only the clock
  changed, the plan stays LOCAL and marks the old and new boxes.
- A pinned, running or title change on the same tick goes FULL.
- If either set of boxes is unknown or their shapes differ, the plan goes
  FULL.
- The frame key now folds in the lane, the theme id and palette, the
  degraded window count and the ids of the windows whose content resolved.
  A host-gpu present
  (`record_host_lane_present`), late content, or a theme switch therefore
  goes FULL.

A window that overlaps the clock is replayed through the window's own layer
(`engine2d_retained_damage_replay_differs_from_full_frame_on_vulkan_embedded_surfaces_2026-11-26`).

## Evidence
All runs used seed fb80903917d6d5f5 on Linux aarch64.
- **Red:** on the pre-fix code, `wm_retained_clock_tick_spec` example 1
  fails with "expected software to equal software-retained-damage". A
  mutant with no theme or content in the frame key, and a no-op host-lane
  record, fails examples 3 and 5.
- **Green:**
  - `wm_retained_clock_tick_spec` 5/5. It uses the production taskbar shape
    and the real `simpleos_runtime_taskbar_revision` caller shape.
  - `wm_retained_damage_behavior_spec` 8/8.
  - `engine2d_wm_local_lane_clock_tick_spec` 2/2 on NVIDIA GB10 and on
    llvmpipe, with `SIMPLE_2D_REQUIRE_VULKAN=1`. The scene has a focused
    140x84 window under the clock. The checks:
    - a fresh full device readback, with a canary pixel, equals a fresh
      Vulkan executor frame of the new tick;
    - pixels outside the clock boxes are unchanged;
    - the glyphs changed and the window is present.
  - The fluid_light example falls back to FULL, which is honest
    (parent-sampling material is tracked separately).
- **Perf** at `Engine2dWmFrameExecutor.render` on GB10, 160x120 Vulkan,
  production taskbar, 3 rounds with alternated order, base 16caf04da27:

  | Case | Base | Branch |
  |---|---|---|
  | Window misses the clock box | 5.42-5.48 s | 52-54 ms |
  | Window under the clock, focused | 5.72-5.78 s | 5.68-5.72 s |
  | Window under the clock, unfocused (930) | 5.71-5.76 s | 5.68-5.71 s |

  - On the window-under-clock rows the window's layer dominates. The change
    is within 1%, so no regression, but also no win.
  - A forced full repaint mid-probe costs the full ~5.5 s again, as
    expected.
  - The earlier 134-157 ms figure is withdrawn: it was measured with the
    window dropped and an empty tray.

## Still open
- The window-overlap tick costs as much as a full frame, because each
  replay creates and reads back a whole layer for the surface.
- fluid_light (parent-sampling window material) always repaints in full;
  this is tracked as
  `wm_retained_damage_rejects_parent_sampling_window_material_2026-11-26`.

## Content updates and moves (review follow-up, 2026-11-27)
The frame key now pins only the set of window ids whose content resolved,
not their content URIs.
- When a window's content URI changes (a new content_revision, or a frame
  re-stamped after a move or focus change), only that window's full bounds
  are damaged.
- An id that doesn't match a scene window fails closed to FULL.
- Layout-key fields percent-escape `%`, `|` and `;`.

Evidence, through `render()`: `wm_retained_clock_tick_spec` 8/8.
- A content update (same scene revision, content_revision 1 -> 2, new
  pixels) takes `software-retained-damage` and equals a fresh executor
  frame.
- A move (scene revision 7 -> 8, x 10 -> 40) takes
  `software-retained-damage` and equals a fresh executor frame.
- Red: on ee1c5b9100c, the URI-keyed frame key fails both examples (the
  path stays `software`), and the separator-escape example fails too.
- The clock device spec adds aetheric_dark, which fails closed to FULL like
  fluid_light (parent-sampling glass).

Perf note: any replay that touches a window costs about a full frame on
Vulkan, because the window's layer is created, rendered and read back. See
`engine2d_retained_damage_replay_differs_from_full_frame_on_vulkan_embedded_surfaces_2026-11-26`.
