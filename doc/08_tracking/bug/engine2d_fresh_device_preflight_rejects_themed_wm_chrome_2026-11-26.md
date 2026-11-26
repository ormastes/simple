# BUG: strict fresh-device preflight rejects the themed WM chrome stream

Status: OPEN (2026-11-26).
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
