# GUI Showcase 4K 200 FPS JIT Lowering Blocker

- Date: 2026-06-22
- Status: fixed
- Gate: `scripts/check/check-widget-showcase-4k-200fps.shs`
- Evidence: `build/widget-showcase-4k-200fps/status.env`

## Problem

The 4K widget showcase performance gate previously split into two facts:

- retained static-frame presentation exceeded 200 FPS in the native alias;
- native readback proof was invalid (`pixels=1`, nonblank/checksum
  unverified), so the gate correctly remained failed.

Interpreter/JIT path falls back to the interpreter:

```text
HIR lowering error: Memory safety error [W1006]: mutation without mut capability:
mutation requires `mut` capability while lowering _emu_sort_i32 at 75:24
```

Native alias path originally built but crashed before readback:

```text
gui_showcase_4k_200fps_status=fail
gui_showcase_4k_200fps_reason=native-showcase-probe-failed
gui_showcase_4k_200fps_probe_exit_code=139
```

The app-specific `W_dot_to_u32`/`H_dot_to_u32` unresolved native stubs were
removed from `widget_showcase_gui.spl`, but `two_line_2d_gui.spl` compiled with
the same native-build settings also segfaults after `CpuBackend` startup. This
points at the native Engine2D CPU backend/runtime path, not only the showcase.

Resolved evidence:

```text
gui_showcase_4k_200fps_status=pass
gui_showcase_4k_200fps_reason=met-200fps
gui_showcase_4k_200fps_width=3840
gui_showcase_4k_200fps_height=2160
gui_showcase_4k_200fps_frames=200
gui_showcase_4k_200fps_elapsed_ns=372385925
gui_showcase_4k_200fps_fps_x1000=537077
gui_showcase_4k_200fps_render_mode=retained-static-frame
gui_showcase_4k_200fps_redraw_frames=1
gui_showcase_4k_200fps_pixels=8294400
gui_showcase_4k_200fps_nonzero_pixels=5534
gui_showcase_4k_200fps_checksum=23682403523276
```

## Fix

The native C runtime `rt_array_repeat` helper receives a raw `i64` count from
native codegen. It decoded tag-shaped raw counts with `rt_core_numeric_arg`, so
4K `u32` repeat buffers used by `SoftwareBackend.init()` shrank by `/8`.
`rt_array_repeat` now uses the raw count directly. The showcase probe uses
`SoftwareBackend.read_pixels()` and records full-scan nonblank/checksum
evidence. The gate remains the default 4K/200 FPS check and now also supports
`RESOLUTION=8k` for retained 8K evidence through the same native alias path.
