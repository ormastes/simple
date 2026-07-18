# GUI/Web/2D Vulkan Browser Backing Evidence - 2026-06-27

## Scope

Focused Linux browser-backing proof for Chrome and Electron Chromium Vulkan
backing, plus aggregate provenance preservation for the Simple binary selected
by the setup wrapper.

## Commands

Focused browser-backing setup:

```sh
BUILD_DIR=build/live-gui-web-2d-vulkan-browser-backing TIMEOUT_SECS=35 \
  sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing
```

Aggregate consumption:

```sh
GUI_WEB_2D_VULKAN_BROWSER_BACKING_ENV=build/live-gui-web-2d-vulkan-browser-backing/evidence.env \
  sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## Evidence Summary

- Simple binary: `release/x86_64-unknown-linux-gnu/simple`
- Simple binary selection reason: `self-hosted-release`
- Simple binary status: `pass`
- Electron ARGB status: `pass`, 1280x720, nonblank
- Electron Vulkan status: `pass`
- Electron browser backing status: `pass`
- Electron browser backing reason: `electron-vulkan-backed`
- Electron Vulkan flag: `enabled_on`
- Electron GPU compositing: `enabled`
- Electron GL implementation: `(gl=egl-angle,angle=vulkan)`
- Electron Skia backend: `GaneshVulkan`
- Electron renderer: `ANGLE (NVIDIA, Vulkan 1.4.312 (NVIDIA NVIDIA TITAN RTX (0x00001E02)), NVIDIA-580.126.16.0)`
- Chrome ARGB status: `pass`, 1280x720, nonblank
- Chrome Vulkan status: `not-rejected-by-log`
- Chrome browser backing status: `pass`
- Chrome browser backing reason: `chrome-vulkan-backed`
- Chrome GPU compositing: `enabled`
- Chrome GL implementation: `(gl=egl-angle,angle=vulkan)`
- Chrome Skia backend: `GaneshVulkan`
- Chrome renderer: `ANGLE (NVIDIA, Vulkan 1.4.312 (NVIDIA NVIDIA TITAN RTX (0x00001E02)), NVIDIA-580.126.16.0)`
- Overall browser backing status: `pass`
- Overall browser backing reason: `pass`
- Browser backing mode: `gpu-feature-status`

## Result

The browser-backing lane proves Electron Chromium and Chrome are Vulkan-backed
on this Linux host for the focused setup. The aggregate audit now preserves the
Simple binary provenance from browser-backing evidence when runtime evidence is
not also supplied.

The broader GUI RenderDoc feature coverage and GUI widget RenderDoc goal remain
incomplete until the full RenderDoc, widget, and cross-surface comparison gates
produce passing evidence.
