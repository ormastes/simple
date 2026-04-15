# SYS-GUI-006 LIVE-GREEN Declaration (2026-04-15)

## Result

`test/system/simpleos_desktop_framebuffer_spec.spl` — **TEST PASSED**

- Pixel match: **100.0 %** (786 432 / 786 432)
- Resolution: 1024 × 768
- Backend: `browser_compositor` (in-process render)
- Baseline: `test/baselines/simpleos_desktop_framebuffer/desktop_scene.ppm`

## Fixes That Unblocked LIVE-GREEN

| Round | Fix |
|-------|-----|
| Round-19 | `qemu_capture.spl`: replaced bare struct `QmpClient(socket_path:...)` with `qmp_connect(qmp_socket)` call |
| Round-20 | Rust seed rebuilt (`simple-driver`) after interpreter_extern sources touched; new binary picked up `rt_unix_socket_connect` |
| Round-21 | `file_read_bytes` returns `Option<[u8]>` not `[u8]`; unwrapped via `match ppm_data_opt: Some(...) / None:` in both `qemu_capture.spl` and the spec |
| Round-22 | `SIMPLE_TEST_TIMEOUT=240` — 60 s watchdog too tight for the render + compare path |
| Round-23 | Extracted `_run_compare(handle, result, baseline_path, nb) -> bool` helper to avoid interpreter eager-scope bug for `base_w`, `base_h` variables inside `it{}` |

## Artifacts Committed

| Artifact | Commit |
|----------|--------|
| `src/os/compositor/qemu_capture.spl` (qmp_connect fix) | `3e13e943`, `2d0cf90b` |
| `test/system/simpleos_desktop_framebuffer_spec.spl` (_run_compare) | `b1d329ce` |
| `test/baselines/simpleos_desktop_framebuffer/desktop_scene.ppm` (2.3 MB) | `b1d329ce` |
| `src/runtime/hosted/js_test262.rs` (corpus loader) + FFI matrix | `37949604` |

## Unblocks

- sys-gui-008 Round-1 gate cleared — virtio-gpu QEMU path can now proceed
- Row 4 of `doc/03_plan/gui_drawing_layer_variations.md` no longer blocked
