# Simple 2D showcase expert wiki

Use this page for `graphics_2d_showcase` changes and verification.

The gallery demonstrates Engine2D primitives, selected vector-font text, and
ordered `std.gpu.engine2d.compositor` planes: desktop, child window, taskbar.
It does not claim to be the WM; the real WM owns widget nesting and window
lifecycle. Host Winit events must enter `common.io.window_event.WindowEventLoop`
before interaction state changes. Do not add private input or font routes.

For DrawIR-backed follow-up surfaces, use canonical DrawIR composition and its
event-target handoff. Keep transient font atlas/cache material out of DrawIR.

Performance proof requires >=60 changed-frame redraws, exact backend identity,
p95 <=33.33 ms, and a changed checksum. A static `present()` loop is invalid.
Live proof also requires actual window identity, nonblank pixels, normalized
key/pointer/click delivery, and a post-input pixel change.

See `doc/07_guide/ui/showcase_apps.md` and
`test/03_system/app/simple_2d/feature/graphics_2d_showcase_spec.spl`.
