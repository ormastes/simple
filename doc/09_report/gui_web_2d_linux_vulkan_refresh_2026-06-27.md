# GUI/Web/2D Linux Vulkan Refresh - 2026-06-27

## Summary

The current Linux host has hardware Vulkan (`NVIDIA TITAN RTX`) and can produce
passing Electron, Chrome, and Simple GUI/web/2D Vulkan comparison evidence after
installing ignored Electron dependencies under `tools/electron-shell/node_modules`.

The combined aggregate run accepts browser Vulkan backing, direct ARGB
comparison artifacts, pairwise pixel equivalence, Web WM modern shell evidence,
and refreshed 4K/8K retained performance rows. The aggregate remains incomplete
because native RenderDoc `.rdc`, platform render-log, production parity, Metal,
and full CSS gates are still open.

## Commands

```sh
npm install --prefix tools/electron-shell

ALLOW_PATH_SIMPLE_BIN=1 \
BUILD_DIR=build/gui-web-2d-vulkan-env-browser-backing-current-refresh-electron \
GUI_WEB_2D_VULKAN_TIMEOUT_SECS=60 \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing

ALLOW_PATH_SIMPLE_BIN=1 \
BUILD_DIR=build/gui-web-2d-vulkan-env-run-current-refresh-electron \
GUI_WEB_2D_VULKAN_TIMEOUT_SECS=90 \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run

GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-current-2026-06-27-refresh/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-current-2026-06-27-refresh/status.env \
GUI_WEB_2D_VULKAN_ENV=build/gui-web-2d-vulkan-env-check-current-refresh/evidence.env \
GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-browser-backing-current-refresh-electron/evidence.env \
GUI_WEB_2D_VULKAN_RUN_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-run-current-refresh-electron/evidence.env \
BUILD_DIR=build/gui-renderdoc-current-2026-06-27-linux-vulkan-refresh \
REPORT_PATH=build/gui-renderdoc-current-2026-06-27-linux-vulkan-refresh/report.md \
GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/gui-renderdoc-current-2026-06-27-linux-vulkan-refresh-cache \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## Accepted Rows

| Evidence | Status |
| --- | --- |
| `web_wm_modern_shell_evidence_status` | `pass` |
| `gui_web_2d_vulkan_browser_backing_status` | `pass` |
| `gui_web_2d_vulkan_electron_browser_backing_status` | `pass` |
| `gui_web_2d_vulkan_chrome_browser_backing_status` | `pass` |
| `gui_web_2d_vulkan_comparison_artifact_status` | `pass` |
| `gui_web_2d_vulkan_simple_backend_status` | `pass` |
| `gui_web_2d_vulkan_pixel_comparison_status` | `pass` |
| `gui_web_2d_vulkan_pixel_comparison_mode` | `pairwise-argb-diff` |
| `gui_web_2d_vulkan_electron_chrome_pairwise_diff_status` | `pass` |
| `gui_web_2d_vulkan_electron_simple_pairwise_diff_status` | `pass` |
| `gui_web_2d_vulkan_chrome_simple_pairwise_diff_status` | `pass` |
| `gui_showcase_4k_200fps_status` | `pass` |
| `gui_showcase_8k_perf_status` | `pass` |

## Remaining Blockers

`blocked_completion_gate_count=10`:

- Simple Vulkan Engine2D RenderDoc `.rdc` with `RDOC` magic.
- Original Chrome-on-Vulkan RenderDoc `.rdc` with `RDOC` magic.
- Electron Chromium-on-Vulkan RenderDoc `.rdc` with nonblank ARGB render proof.
- Simple GUI widget RenderDoc `.rdc` on Vulkan Engine2D.
- Electron Chromium-on-Vulkan widget RenderDoc `.rdc` with nonblank ARGB proof.
- Native render-log comparison for Linux Vulkan, macOS Metal, and Windows D3D12.
- Production GUI/web font offload readback evidence.
- Production GUI/web raw Metal readback evidence.
- Production GUI/web parity evidence with live Tauri and Chrome captures.
- Full CSS specification rendering coverage beyond implemented Simple Web subset.

## Boundary

This report proves the current Linux browser-backing, ARGB pairwise, Web WM, and
retained performance gates that can run without RenderDoc. It does not prove
RenderDoc capture, PIX/GPU debugger capture, macOS Metal, Windows D3D12, or full
CSS support.
