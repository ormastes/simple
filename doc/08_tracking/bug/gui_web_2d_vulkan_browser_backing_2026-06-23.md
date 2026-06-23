# Bug: GUI/web/2D browser Vulkan backing is not proven

Status: open
Date: 2026-06-23
Area: GUI/web/2D Vulkan, Electron/Chrome browser backing

## Symptom

The aggregate GUI audit must stay incomplete when:

- `gui_web_2d_vulkan_browser_backing_status` is not `pass`
- `gui_web_2d_vulkan_browser_backing_mode=fallback-bitmap-comparison`
- Electron or Chrome reports `vulkan-angle-unavailable`

A rendered bitmap is useful fallback evidence, but it is not proof that the
browser process was Vulkan-backed.

## Required Evidence

Completion requires `scripts/setup/setup-gui-web-2d-vulkan-env.shs
--browser-backing` or the aggregate GUI audit to prove:

- `gui_web_2d_vulkan_browser_backing_status=pass`
- `gui_web_2d_vulkan_browser_backing_mode=gpu-feature-status` or stronger
  RenderDoc-backed browser evidence
- Electron and Chrome both report Vulkan-backed GPU feature status
- logs do not contain Chromium `angle=vulkan` unavailable failures

Keep `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` incomplete
until those keys pass.
