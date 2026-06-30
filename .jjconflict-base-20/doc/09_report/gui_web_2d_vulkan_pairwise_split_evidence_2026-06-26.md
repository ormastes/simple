# GUI/Web/2D Vulkan Split Pairwise Evidence - 2026-06-26

## Scope

This report records Linux GUI/web/2D Vulkan progress after isolating focused
browser-backing evidence from direct pairwise evidence. It proves Electron
Chromium, Chrome, and Simple Vulkan ARGB captures can match exactly on this
host when the shared fixture contains no pairwise-visible browser-only animation
or WebGL mutation.

This does not prove strict RenderDoc completion because `renderdoccmd` is not
available on this host, so `.rdc` artifacts with `RDOC` magic are still missing.

## Commands

```sh
npm install

BUILD_DIR=build/gui-web-2d-vulkan-env-browser-backing-next TIMEOUT_SECS=60 \
  sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing

BUILD_DIR=build/gui-web-2d-vulkan-env-run-next TIMEOUT_SECS=60 \
  sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run

BUILD_DIR=build/linux-vulkan-render-log-compare-next-diagnostic \
REPORT_PATH=build/linux-vulkan-render-log-compare-next-diagnostic/report.md \
GUI_WEB_2D_VULKAN_ENV=build/gui-web-2d-vulkan-env-run-next/evidence.env \
GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-browser-backing-next/evidence.env \
LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=0 \
  sh scripts/check/check-linux-vulkan-render-log-compare.shs

BUILD_DIR=build/linux-vulkan-render-log-compare-next-strict \
REPORT_PATH=build/linux-vulkan-render-log-compare-next-strict/report.md \
GUI_WEB_2D_VULKAN_ENV=build/gui-web-2d-vulkan-env-run-next/evidence.env \
GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-browser-backing-next/evidence.env \
  sh scripts/check/check-linux-vulkan-render-log-compare.shs || true
```

## Evidence

- Electron browser backing: `pass`, `electron-vulkan-backed`
- Chrome browser backing: `pass`, `chrome-vulkan-backed`
- Electron ARGB checksum: `3956812989604346`
- Chrome ARGB checksum: `3956812989604346`
- Simple ARGB checksum: `3956812989604346`
- Electron/Chrome pairwise mismatch count: `0`
- Electron/Simple pairwise mismatch count: `0`
- Chrome/Simple pairwise mismatch count: `0`
- Pixel comparison: `pass`, `pairwise-argb-diff`
- Diagnostic Linux render-log compare: `pass`
- Strict Linux render-log compare: `fail`, blocked only by
  `renderdoc-simple-rdc,renderdoc-chrome-rdc,renderdoc-electron-rdc`

## Implementation Notes

- `scripts/setup/setup-gui-web-2d-vulkan-env.shs` now honors `BUILD_DIR` and
  `TIMEOUT_SECS`, matching other repo wrappers. This keeps `--browser-backing`
  and `--run` evidence from overwriting each other.
- The shared generated GUI/Vulkan fixture keeps the RenderDoc marker IDs but
  hides the browser-only pulse probes from pairwise-visible pixels. That avoids
  false pixel mismatches caused by JavaScript/WebGL execution differences
  between Electron, Chrome, and the static Simple HTML renderer.

## Remaining Blocker

Install or expose `renderdoccmd`, then rerun the Simple, Chrome, and Electron
RenderDoc capture lanes so strict Linux render-log comparison can require real
`.rdc` artifacts whose first four bytes are `RDOC`.
