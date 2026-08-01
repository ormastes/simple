<!-- codex-design -->
# Showcase apps detail design

Shared interfaces:

- `showcase_catalog() -> [ShowcaseEntry]`
- `launch_showcase(app_id, surface) -> Result<ShowcaseLaunch, ShowcaseError>`
- app IDs: `graphics_2d_showcase`, `web_standards_showcase`, `gui_widget_showcase`
- surfaces: `standalone`, `host_wm`, `simpleos_wm`

Manual flow helpers use these visible steps: “Open the showcase catalog”, “Launch the showcase”, “Exercise visible controls”, “Verify rendered output”, “Verify the same app in host WM”, and “Verify the same app in SimpleOS WM”. Setup/checker helpers must fail fast when a requested surface, event route, backend handle, or readback is absent.

The 2D scene is divided into labeled primitive, raster/image/text, transform/clip, and blend sections. The web page is `examples/06_io/ui/browser_common_elements_showcase.html`. The GUI scene retains the existing widget gallery and exposes semantic state for every interactive control.

Errors carry app ID, surface, phase, and backend/transport cause. A blank frame, synthetic handle, CPU mirror presented as GPU readback, static source check, or unavailable window reported as success is an error.

For the 2D showcase, compose three Engine2D layers in z order
`desktop < child < taskbar`, then draw the compositor output as a gallery
primitive. Convert raw Winit batches into `WindowEventRecord`s, drain the
shared loop, and derive interaction counts/state only from drained events.
The performance route redraws a visible overlay for at least 60 samples and
requires p95 <=33.33 ms plus a checksum change; it is separate from a live
window acceptance capture.
