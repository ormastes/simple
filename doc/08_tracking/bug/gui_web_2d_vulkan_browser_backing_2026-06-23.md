# Bug: GUI/web/2D browser Vulkan backing is not proven

Status: open
Date: 2026-06-23
Area: GUI/web/2D Vulkan, Electron/Chrome browser backing

## Symptom

The aggregate GUI audit must stay incomplete when:

- `gui_web_2d_vulkan_browser_backing_status` is not `pass`
- `gui_web_2d_vulkan_browser_backing_mode` reports fallback, missing focused
  proof, or failing `gpu-feature-status`
- Electron or Chrome reports `vulkan-angle-unavailable`

A rendered bitmap, exact pixel parity, or pairwise Simple/Chrome/Electron
bitmap comparison is useful fallback evidence, but it is not proof that the
browser process was Vulkan-backed. Missing focused browser proof must remain a
failed browser-backing gate, not a successful fallback bitmap comparison.

## Current Evidence

`scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing` is now a
valid focused probe mode. The 2026-06-26 Linux host run passes after upgrading
the repo-local Electron shell to Electron 42, adding `--ozone-platform=x11` to
the Electron Vulkan launch, and sampling Electron GPU status after the page is
captured:

```text
gui_web_2d_vulkan_mode=--browser-backing
gui_web_2d_vulkan_browser_backing_mode=gpu-feature-status
gui_web_2d_vulkan_electron_browser_backing_status=pass
gui_web_2d_vulkan_electron_browser_backing_reason=electron-vulkan-backed
gui_web_2d_vulkan_electron_browser_backing_vulkan=enabled_on
gui_web_2d_vulkan_chrome_browser_backing_status=pass
gui_web_2d_vulkan_chrome_browser_backing_reason=chrome-vulkan-backed
gui_web_2d_vulkan_browser_backing_status=pass
gui_web_2d_vulkan_browser_backing_reason=pass
```

When the focused browser proof is absent, the gate must report:

```text
gui_web_2d_vulkan_browser_backing_mode=focused-browser-backing-required
gui_web_2d_vulkan_browser_backing_reason=missing-focused-browser-backing
```

## Required Evidence

Completion requires `scripts/setup/setup-gui-web-2d-vulkan-env.shs
--browser-backing` or the aggregate GUI audit to prove:

- `gui_web_2d_vulkan_browser_backing_status=pass`
- `gui_web_2d_vulkan_browser_backing_mode=gpu-feature-status` or stronger
  RenderDoc-backed browser evidence, not `focused-browser-backing-required`
- Electron and Chrome both report Vulkan-backed GPU feature status
- logs do not contain Chromium `angle=vulkan` unavailable failures

Keep `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` incomplete
until those keys pass.
