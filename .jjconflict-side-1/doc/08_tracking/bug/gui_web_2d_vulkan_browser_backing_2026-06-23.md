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
valid focused probe mode. The 2026-06-26 Linux host run proves Chrome is
Vulkan-backed, but still fails the browser-backing rollup because Electron does
not prove ANGLE/Vulkan renderer backing. Electron reports `vulkan=enabled_on`
and GPU compositing enabled, but the compact proof has
`hardwareSupportsVulkan=false`, `glImplementationParts=(gl=none,angle=none)`,
`skiaBackendType=None`, and an empty GL renderer:

```text
gui_web_2d_vulkan_mode=--browser-backing
gui_web_2d_vulkan_browser_backing_mode=gpu-feature-status
gui_web_2d_vulkan_electron_browser_backing_status=fail
gui_web_2d_vulkan_electron_browser_backing_reason=electron-vulkan-enabled-without-angle-vulkan-proof
gui_web_2d_vulkan_electron_browser_backing_vulkan=enabled_on
gui_web_2d_vulkan_electron_browser_backing_gpu_compositing=enabled
gui_web_2d_vulkan_electron_browser_backing_hardware_supports_vulkan=false
gui_web_2d_vulkan_electron_browser_backing_gl_implementation_parts=(gl=none,angle=none)
gui_web_2d_vulkan_electron_browser_backing_skia_backend_type=None
gui_web_2d_vulkan_chrome_browser_backing_status=pass
gui_web_2d_vulkan_chrome_browser_backing_reason=chrome-vulkan-backed
gui_web_2d_vulkan_chrome_browser_backing_display_type=ANGLE_VULKAN
gui_web_2d_vulkan_chrome_browser_backing_skia_backend_type=GaneshVulkan
gui_web_2d_vulkan_browser_backing_status=fail
gui_web_2d_vulkan_browser_backing_reason=electron-vulkan-enabled-without-angle-vulkan-proof;chrome-vulkan-backed
```

A bounded flag probe on the same host wrote evidence under
`build/electron-vulkan-flag-probe-2026-06-26/` and did not find an Electron
flag-only fix:

```text
x11: exit=0 vulkan=enabled_on gpu=enabled hardware=false gl=(gl=none,angle=none) skia=None
no-ozone: exit=0 vulkan=enabled_on gpu=enabled hardware=false gl=(gl=none,angle=none) skia=None
headless: exit=1 vulkan= gpu= hardware=undefined gl= skia=
```

That makes the next actionable work an Electron host/runtime proof change
(for example a real desktop GPU host, a different Electron/Chromium GPU stack,
or a CDP/SystemInfo-backed Electron proof if Electron can expose it), not simply
adding more launch flags to the current Xvfb run.

An in-process Electron page-debugger CDP probe is also not sufficient. Calling
`SystemInfo.getInfo` through `win.webContents.debugger` returns
`SystemInfo.getInfo is only supported on the browser target`, so a CDP-based
Electron proof must connect to Electron's browser-level DevTools target, not a
page target.

The capture tool now supports that browser-target CDP path through
`ELECTRON_CAPTURE_REMOTE_DEBUGGING_PORT`. On the current Linux Xvfb host the
browser target is reachable and reports
`gui_web_2d_vulkan_electron_browser_backing_browser_target_gpu_info_status=pass`,
but it still does not prove Vulkan backing: `hardwareSupportsVulkan=false` and
renderer fields remain empty or fall back to app-level `(gl=none,angle=none)`
and `skia=None`.

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
- Electron and Chrome both report Vulkan-backed GPU feature status and renderer
  proof: enabled GPU compositing, `hardwareSupportsVulkan=true`, and Vulkan in
  display type, GL implementation parts, Skia backend, or GL renderer
- logs do not contain Chromium `angle=vulkan` unavailable failures

Keep `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` incomplete
until those keys pass.
