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
