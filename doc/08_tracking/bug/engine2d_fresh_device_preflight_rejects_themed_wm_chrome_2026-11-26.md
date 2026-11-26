# BUG: strict fresh-device preflight rejects the themed WM chrome stream

Status: VERIFIED 2026-11-26 (fixed on work/bug-engine2d-themed-preflight-20261126).
Where: `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`
`_engine2d_draw_ir_fresh_device_reason` ->
`_engine2d_draw_ir_fresh_device_command_supported`; consumer
`src/app/simpleos_gpu_host/daemon_runner.spl:409`.
Spec: `test/02_integration/rendering/engine2d_themed_wm_fresh_device_spec.spl`

## Measured (Linux aarch64, seed cargo-target-wr-seed1126b)

Both production WM bootstraps install a theme snapshot before the first frame
(`host_wm_theme_bootstrap` -> registry default `fluid_light`;
`simpleos_wm_theme_bootstrap` -> generated `fluid_light`), so the themed
stream (styled body/titlebar boxes, rounded traffic lights, resolved text) is
what users see. For the canonical 160x120 one-window scene:

| stream | device | readback_source | skipped | reason |
|---|---|---|---|---|
| fluid_light themed | NVIDIA GB10 | preflight_rejected | 1 | `fresh-device-command-preflight-required` |
| aetheric_dark themed | NVIDIA GB10 | preflight_rejected | 1 | same |
| fluid_light / aetheric_dark themed | llvmpipe (LLVM 20.1.2) | preflight_rejected | 1 | same |
| no-package plain stream | NVIDIA GB10 and llvmpipe | device_readback | 0 | — (pixels == CPU) |

So the strict device path can only composite the no-package stream; any
themed WM frame given to it (e.g. the SimpleOS GPU host daemon) is refused.

Also observed: both generated snapshots declare window shadow layers
(`ThemeShadowLayer`, e.g. fluid_light offset_y 28, blur 76), but the CPU
composition paints no shadow at the window's right margin (pixel (130,70)
equals the desktop pixel at (135,70)); the no-package stream does paint one.
The themed stream emits no `win-shadow` rect by design: its shadow is carried
as box-shadow in the body's `computed_style` (executed by
`engine2d_draw_ir_typed_box_shadows`), inside a window embedding that only
reserves a 5x4 px margin. Whether that margin should show it is unverified.

## Next step

Identify which themed command(s) fail `_engine2d_draw_ir_fresh_device_command_supported`
(styled boxes with `computed_style`, `_wm_aqua_rounded_box`, styled text) and
either extend the checked device kernels or route those commands through a
checked fallback; then turn the spec's device arm green.

## Root cause and fix 2026-11-26

Per-command preflight probe on the fluid_light stream: every `window-win`
command (styled body/titlebar, rounded traffic lights, resolved text) already
passed. The only rejected commands were two STYLE-FREE translucent rects in
the full-target `wm-chrome` batch: `command-lane` (0,0 160x32) and `taskbar`
(0,72 160x48), both `0xB8FFFFFF`. The preflight only allowed a translucent rect
as the first command of a clipped child; on a full-target batch it demanded
alpha 0xFF, a rule that predates `ef102ac6ae1` (Vulkan translucent rects now
composite on the GPU via blend_solid mode 2, byte-identical to CPU over an
opaque destination).

Fix (`_engine2d_draw_ir_fresh_device_reason`): when the caller opts in
(`admit_translucent_root_rects`, passed only by
`engine2d_draw_ir_adv_fresh_device_composition_with_images`), a style-free
translucent rect is admitted in a full-target, opacity-1000, non-CSS-group
batch (executed directly on the root, `fills_target_exactly`) after the opaque
initializer. Styled/masked translucent rects stay rejected; the retained
damage replay and tile wrappers do not opt in and keep the opaque-only rule
(not proven under their clips).

Shadow: the themed `win-body` carries the shadow as the legacy aggregate
box-shadow style (no typed shadow schema: `schema_present=false`), admitted
via `engine2d_draw_ir_legacy_shadow_safe`; it was never the rejected command,
and it is not visible in this scene's 5x4 px window margin.

Evidence (Linux aarch64, seed cargo-target-wr-seed1126b):

- `engine2d_themed_wm_fresh_device_spec.spl` (no longer in-development):
  base 0/3 -> fixed, on NVIDIA GB10 and llvmpipe (LLVM 20.1.2); fluid_light
  and aetheric_dark themed windows: `device_readback`, skipped 0,
  rendered 16, fallback_required false, 0 of 19200 pixels differ from CPU.
- An opaque image initializer plus a style-free translucent rect (the old
  "mixed" rejection instance) is also device == CPU on both ICDs; that
  `engine2d_embedded_surface_spec` example now uses a rounded translucent
  rect, which is still rejected.
- Pre-existing reds unchanged before/after (identical failing examples):
  draw_ir_adv_spec 69/70, simpleos_host_gpu_image_execution_contract 0/3,
  simpleos_vulkan_io_interface_contract 8/9;
  engine2d_font_surface_verification executes 0 examples on both sides;
  gui_content_renderer 5/5 and backend_vulkan_blend_cpu_parity 10/10 green.

Perf (plain stream, admitted on both sides; 20 fresh-device frames on NVIDIA
GB10 per run, interpreter seed sha256 fb80903917d6d5f5, 3 rounds, base run
first each round): base 7.24/6.10/5.88 s/frame (mean 6.41), patched
6.44/5.84/6.22 (mean 6.17). The spread (~10%) is run-order and host noise; the
change adds one boolean test per command and no measurable cost. The themed
stream's device time is a new capability (it was rejected before).
