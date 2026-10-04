# 2D GPU showcase on Vulkan at 3840x2160 skips two commands with no fallback reason

- **Filed:** 2026-10-05
- **Area:** `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` (composition executor)
  × `src/app/ui_showcase/hosts/host_2d_gpu.spl` (receipt check)
- **Status:** FIXED 2026-10-05 for the engine2d executor and the showcase hosts;
  other strict consumers listed below remain open

## Repro (before)

```
SIMPLE_GPU_BACKEND=vulkan SIMPLE_SHOWCASE_W=3840 SIMPLE_SHOWCASE_H=2160 \
SIMPLE_SHOWCASE_FRAMES=1 <seed> run src/app/ui_showcase/hosts/main_2d_gpu.spl
showcase status=fail renderer=vulkan reason=metal-drawir-receipt-rejected
```

The result was valid except for `skipped_command_count=2`, and the skips
carried no `fallback_reason`. The same scene passed at 320x240.

## Root cause

Neither skip is a render failure. Both are **occlusion culls**:

```
OCCLUDED kind=rect id=sc2d_vulkan_panel_left-scrollbar-track  box=1912,24,8x692
OCCLUDED kind=rect id=sc2d_vulkan_panel_right-scrollbar-track box=3830,24,8x692
```

At 4K all rows fit, so each scrollbar thumb covers its whole track, and
`_engine2d_draw_ir_render_command_plan`'s exact occlusion proof
(`prove_occlusion`) correctly culls the invisible track. The executor counts a
cull in `skipped`, the same convention as damage culling
(`ops_culled_by_damage`). It never reported that count separately, so the
strict host receipt (`skipped_command_count != 0`) could not tell a
pixel-exact cull from a command that failed to render.

The same check also gated the Vulkan window present
(`engine2d_draw_ir_adv_composition_with_images_present` path): a frame with a
proven cull was never presented.

## Fix

- `Engine2dDrawIrRenderOutcome.occluded` counts occlusion-culled logical
  operations at the walker. It is carried through the embedded, direct and
  offscreen batch paths into `Engine2dDrawIrAdvResult.occluded_command_count`.
  `skipped_command_count` keeps its meaning (culls included), so every
  existing consumer sees identical numbers.
- The two showcase hosts (`host_2d_gpu`, `host_2d_engine`) and the
  window-present gate now accept a skip only when every skipped operation was
  occlusion-culled: `skipped_command_count != occluded_command_count`. This
  is not weaker: any non-occlusion skip is still rejected.

## Other strict consumers

Switched to `skipped_command_count != occluded_command_count` (2026-10-05,
follow-up PR): `src/lib/gc_async_mut/ui/gui_content_renderer.spl`,
`src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`,
`src/lib/editor/70.backend/gui_sdl_bridge.spl` (its source-contract pin in
`test/03_system/gui/editor_gui_sdl_spec.spl` updated to the new rule).
`host_2d_vulkan` is left unchanged: its strict primitive lane never
occlusion-culls, so `occluded_command_count` is always 0 there.

Still open, routed to the browser_engine owner (same rule, same fix):
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl`
  (several sites) and `simple_web_html_layout_renderer.spl:382`
  (`browser_engine/**`, owned by another lane)

Each should switch to `skipped_command_count != occluded_command_count`.
