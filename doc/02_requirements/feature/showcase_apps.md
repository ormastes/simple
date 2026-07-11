# Showcase apps requirements

The user selected the complete showcase option in the task directive; this document records that selected scope.

- REQ-001: Provide `graphics_2d_showcase`, `web_standards_showcase`, and `gui_widget_showcase` in a shared catalog.
- REQ-002: Launch each app as standalone, host-WM, and installed SimpleOS-WM surfaces without substituting a mock app.
- REQ-003: The 2D app demonstrates the supported Engine2D primitives, text/images, clipping, transforms, alpha/blending, and backend readback; unsupported capabilities are labeled explicitly.
- REQ-004: The web app opens `browser_common_elements_showcase.html` in the real Simple browser and exercises common HTML/CSS plus focus, keyboard, pointer, click, navigation, and scroll.
- REQ-005: The GUI app demonstrates common widgets and real state changes for button, checkbox, switch, slider, progress, focus, window lifecycle, and taskbar/catalog behavior.
- REQ-006: Dummy, white/striped/background-only, synthetic-handle, source-assertion-only, and silent-success paths cannot satisfy showcase verification.
- REQ-007: Guides, architecture/design, SPipe scenarios/manuals, and UI skills document the same catalog identities and verification flow.
