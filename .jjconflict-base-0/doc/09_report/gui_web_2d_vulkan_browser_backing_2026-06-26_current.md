# GUI/Web/2D Vulkan Browser Backing Evidence - 2026-06-26

## Command

```sh
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-browser-backing-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing
```

Aggregate confirmation:

```sh
GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-current-next/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-current-next/status.env \
GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-browser-backing-current/evidence.env \
BUILD_DIR=build/gui-renderdoc-current-browser-backing-pass \
REPORT_PATH=build/gui-renderdoc-current-browser-backing-pass/report.md \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## Result

The focused browser-backing proof passes for both Electron Chromium and Chrome.

| Field | Value |
| --- | --- |
| `gui_web_2d_vulkan_browser_backing_status` | `pass` |
| `gui_web_2d_vulkan_browser_backing_reason` | `pass` |
| `gui_web_2d_vulkan_browser_backing_mode` | `gpu-feature-status` |
| `gui_web_2d_vulkan_electron_browser_backing_status` | `pass` |
| `gui_web_2d_vulkan_electron_browser_backing_reason` | `electron-vulkan-backed` |
| `gui_web_2d_vulkan_electron_browser_backing_vulkan` | `enabled_on` |
| `gui_web_2d_vulkan_electron_browser_backing_display_type` | `ANGLE_VULKAN` |
| `gui_web_2d_vulkan_electron_browser_backing_skia_backend_type` | `GaneshVulkan` |
| `gui_web_2d_vulkan_electron_browser_backing_source_file_status` | `pass` |
| `gui_web_2d_vulkan_electron_browser_backing_argb_source_file_status` | `pass` |
| `gui_web_2d_vulkan_electron_browser_backing_browser_target_gpu_info_status` | `pass` |
| `gui_web_2d_vulkan_chrome_browser_backing_status` | `pass` |
| `gui_web_2d_vulkan_chrome_browser_backing_reason` | `chrome-vulkan-backed` |
| `gui_web_2d_vulkan_chrome_browser_backing_display_type` | `ANGLE_VULKAN` |
| `gui_web_2d_vulkan_chrome_browser_backing_skia_backend_type` | `GaneshVulkan` |
| `gui_web_2d_vulkan_chrome_browser_backing_source_file_status` | `pass` |

Both browser renderers report:

```text
ANGLE (NVIDIA, Vulkan 1.4.312 (NVIDIA NVIDIA TITAN RTX (0x00001E02)), NVIDIA-580.126.16.0)
```

## Aggregate Impact

With this evidence fed through
`GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV`, the aggregate emits:

```text
gui_web_2d_vulkan_browser_backing_status=pass
gui_web_2d_vulkan_electron_browser_backing_status=pass
gui_web_2d_vulkan_chrome_browser_backing_status=pass
```

This report proves browser Vulkan backing only; it is not a RenderDoc, PIX, GPU
debugger, or native platform render-log capture. The earlier aggregate-impact
gap for Linux RenderDoc `.rdc` capture is superseded by
`doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`
and `doc/09_report/linux_vulkan_render_log_compare_current_2026-07-02.md`, which
record zero blocked Linux RenderDoc gates with Simple, Chrome, and Electron
`RDOC` artifacts. Cross-platform native render-log capture and broader CSS
coverage remain separate evidence lanes.
