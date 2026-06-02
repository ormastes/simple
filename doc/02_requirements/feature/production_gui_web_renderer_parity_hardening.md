# Production GUI Web Renderer Parity Hardening Requirements

## Goal

Harden Simple GUI and Simple Web Renderer parity by proving marker-free,
generated `common.ui` widget HTML renders through production renderer paths and
matches Simple Web software, CPU SIMD, and Metal-backed output exactly for the
first production slice.

## Requirements

- REQ-001: Generated GUI HTML must come from real `common.ui` builder and HTML
  widget renderer APIs.
- REQ-002: The production renderer path must reject legacy fixture markers for
  this slice, including exact sample markers, `simple-web-engine2d-*`, known
  font corpus markers, and WM titlebar/content shortcut markers.
- REQ-003: Generated widget HTML must render through
  `simple_web_layout_render_html_pixels`, not the legacy substring heuristic
  renderer.
- REQ-004: The fixture must include text, multiline text, image, and button
  with icon/text content.
- REQ-005: Software, CPU SIMD, and Metal-backed Simple Web Renderer outputs
  must produce full framebuffers with exact pixel parity.
- REQ-006: The evidence must record whether tolerance was used. This slice
  requires `tolerance_used=false`.
- REQ-007: The system spec must fail on fixture marker use, empty framebuffer,
  low color diversity, CPU SIMD mismatch, Metal mismatch, or tolerance use.

## Remaining Scope

Electron/WebKit live reference capture, broader CSS fixture matrices, actual
vectorized CPU SIMD proof, and Metal GPU-readback proof remain open for later
acceptance slices.
