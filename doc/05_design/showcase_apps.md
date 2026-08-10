<!-- codex-design -->
# Showcase apps detail design

Shared interfaces:

- `showcase_catalog() -> [ShowcaseEntry]`
- `launch_showcase(app_id, surface) -> Result<ShowcaseLaunch, ShowcaseError>`
- app IDs: `graphics_2d_showcase`, `web_standards_showcase`, `gui_widget_showcase`
- surfaces: `standalone`, `host_wm`, `simpleos_wm`

Identity contract:

- `graphics_2d_showcase` uses catalog title `2D Rendering Showcase`.
  - standalone title pattern: `2d_showcase_backed_<backend_token>`
  - host/installed title pattern: `2d_showcase_backed_<backend_token>`
- `web_standards_showcase` uses catalog title `Web Standards Showcase`.
  - standalone title pattern: `web_showcase_backed_<backend_token>`
  - host/installed title pattern: `web_showcase_backed_<backend_token>`
- `gui_widget_showcase` uses catalog title `Widget Showcase`.
  - standalone title pattern: `gui_showcase_backed_<backend_token>`
  - host/installed title pattern: `gui_showcase_backed_<backend_token>`

`<backend_token>` is resolved in `showcase_backend_token()` (`cpu`, `software`, `simd`, `cpu_simd`, `cpu-simd`, `simd_cpu`, `simd-cpu`, `vulkan`, `metal`, `tauri`, `electron`, explicit `simple_gui_simple_*`).

Manual flow helpers use these visible steps: “Open the showcase catalog”, “Launch the showcase”, “Exercise visible controls”, “Verify rendered output”, “Verify the same app in host WM”, and “Verify the same app in SimpleOS WM”. Setup/checker helpers must fail fast when a requested surface, event route, backend handle, or readback is absent.

Backend contract:

- `widget_showcase_gui.spl`: CLI flag `--backend=<name>` takes precedence, then `SIMPLE_GUI_BACKEND`, then default `software`.
- `graphics_2d_showcase_gui.spl` and `wm_graphics_2d_showcase_gui.spl`: read `SIMPLE_GUI_BACKEND`; standalone defaults to `software`; host-WM child defaults to `cpu_simd`.
- `web_render_file_gui.spl` and `web_standards_showcase_gui.spl`: read `SIMPLE_GUI_BACKEND`, default `cpu_simd`.

The 2D scene is divided into labeled primitive, raster/image/text, transform/clip, and blend sections. The web page is `examples/06_io/ui/browser_common_elements_showcase.html`. The GUI scene retains the existing widget gallery and exposes semantic state for every interactive control.

Errors carry app ID, surface, phase, and backend/transport cause. A blank frame, synthetic handle, CPU mirror presented as GPU readback, static source check, or unavailable window reported as success is an error.

The ARM64 QEMU fixture renders the canonical graphics core at `752x584` inside
the `2d_showcase_backed_cpu_simd` window. Its live oracle requires the exact
producer identity, all seven shared section labels, four deterministic
primitive-color anchors, detailed palette/nonblank ratios, exact guest/RAMFB
checksum correlation, and ordered input-caused frames. The existing 39 FPS
plus positive-NEON gate remains a release requirement and must be ported and
re-proven on current main before this QEMU slice is marked complete.

## WM showcase: taskbar derivation and capture evidence

Added 2026-08-05 by the documentation lane. **The implementation is owned by a
parallel lane**; the interfaces below were read from the tree on that date, and
each line states whether it is *present* or *intended*.

### Taskbar derivation — present

```
build_taskbar_model(registry: UiWindowSurfaceRegistry,
                    pinned: [AppRef],
                    tray: [TrayItem]) -> TaskbarModel
build_taskbar_model_with_minimized(registry, pinned, tray,
                                   minimized_surface_ids: [text]) -> TaskbarModel
host_taskbar_runtime_taskbar_model(session: UISession) -> TaskbarModel
```

- `build_taskbar_model` is defined at `src/app/ui.web/taskbar_shell.spl:55` and
  builds `running` by iterating `registry.bindings` — the **live** surface
  registry. `host_taskbar_runtime_taskbar_model`
  (`src/app/ui.web/_HostTaskbarRuntime/host_taskbar_runtime.spl:144`) is the
  session-level entry point and passes `session.window_surfaces`.
- `src/lib/common/ui/taskbar_model.spl` is the **schema only**
  (`AppRef`, `WindowRef{…, minimized: bool}`, `TrayItem`, `TaskbarLaunchError`,
  `TaskbarModel{pinned, running, tray}`, `empty_taskbar_model()`); it holds no
  derivation. Serializers `taskbar_model_to_json` and
  `taskbar_model_to_json_with_launch_errors` live beside the builder.
- Only `running` is derived. `pinned` and `tray` are supplied by the caller, and
  pins round-trip through the `SIMPLE_TASKBAR_PINS_V1` line codec in
  `src/lib/common/ui/taskbar_pin_wire.spl` (`taskbar_pin_wire_line`,
  `..._line_valid`, `..._app_id/_display_name/_icon`). That codec performs no
  storage.
- Window lifecycle is the scalar FSM in `src/lib/common/ui/wm_window_state.spl`
  (`NORMAL/MINIMIZED/MAXIMIZED/CLOSING/CLOSED`). `restore` takes the
  pre-minimize state explicitly, so a taskbar restore must carry it.
- **Contract, not yet enforced anywhere:** a taskbar rendered from a literal
  `TaskbarModel` is not evidence of derivation. Two such literals are still in
  the tree (`src/os/desktop/modern_wm_readiness.spl:606`,
  `src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl:148`). A
  derivation claim must show the registry the model came from.

### Capture evidence contract — present

The WM capture lane emits **P6 PPM plus pixel-class counts**, not colour
histograms:

- `src/os/compositor/hosted_wm_capture_evidence.spl` —
  `capture_shared_hosted_wm_frame(path) -> HostedWmCaptureMetrics`
  (`width`, `height`, `pixels`, `non_background_pixels`, `bright_pixels`,
  `accent_pixels`, `sample_checksum`, `render_us`, `theme_id`,
  `theme_source_manifest_sha256`, `backend_evidence`, `write_ok`), with
  `write_argb_crop_ppm_text` and `emit_shared_hosted_wm_ppm_stdout`.
- `src/os/compositor/wm_gui_window_drawing_evidence.spl` — 1024x768 capture,
  `SceneMetrics{… non_bg_pixels, bright_pixels, ink_pixels, accent_pixels,
  max_glyph_run_px, ppm_path}`, including a giant-glyph pathology detector
  (`GIANT_GLYPH_RUN_PX = 40`).
- `src/os/compositor/qemu_capture.spl` — `capture_qemu_inprocess`,
  `decode_qemu_screendump_ppm`, `qemu_screendump_to_file`, `capture_qemu_vm`,
  `probe_qemu_vm_screendump`.
- `src/os/compositor/screenshot_compare.spl` — `compare_pixel_buffers`,
  `compare_exact`, `compare_with_profile`, `compare_per_channel`,
  `find_diff_regions`, `generate_diff_image`.

Pair every comparison with an **absolute oracle** (a known fixed point, a
producer-ran flag, or two independently produced artifacts). A pixel-equality
match between two frames from the same code path proves nothing —
`.claude/skills/spipe.md` §"Equality is not correctness (false-green guard)".

### Not yet verified

- No unified WM-showcase driver module exists; catalog, taskbar, and capture are
  three separate trees.
- `showcase_catalog()` reports **`false` for all nine surface-readiness bits**,
  and `test/01_unit/lib/common/ui/showcase_catalog_spec.spl:55` asserts exactly
  that. Until those bits flip (with the spec updated in the same change), no
  showcase surface is declared launchable, regardless of capture results.
- Whether the WM showcase's taskbar reflects minimize/restore/close **live**
  under a real compositor is unmeasured here; the FSM and the derivation exist
  independently, and their composition has no spec named in this doc.
