# Linux Vulkan Render Log Compare Focused Evidence - 2026-06-28

Focused headless-safe run:

```sh
env BUILD_DIR=build/linux-vulkan-render-log-compare-20260628-focused \
  GUI_WEB_2D_VULKAN_ENV=build/gui-web-2d-vulkan-env/evidence.env \
  GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-browser-backing/evidence.env \
  RDOC_SIMPLE_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-renderdoc-simple/renderdoc/simple/evidence.env \
  RDOC_HTML_EVIDENCE_ENV=build/renderdoc/chrome-display-helper/evidence.env \
  RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/electron-display-helper/electron-html/evidence.env \
  LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=1 \
  sh scripts/check/check-linux-vulkan-render-log-compare.shs
```

Result: `fail`. The non-RenderDoc Linux Vulkan comparison gates pass, but
Chrome and Electron still lack valid RenderDoc `.rdc` artifacts.

Key evidence:

- `linux_vulkan_render_log_compare_status=fail`
- `linux_vulkan_render_log_compare_reason=renderdoc-chrome-fail;renderdoc-electron-fail`
- `linux_vulkan_render_log_compare_blocked_gate_count=2`
- `linux_vulkan_render_log_compare_blocked_gates=renderdoc-chrome-rdc,renderdoc-electron-rdc`
- `linux_vulkan_render_log_compare_simple_vulkan_gate_status=pass`
- `linux_vulkan_render_log_compare_browser_backing_gate_status=pass`
- `linux_vulkan_render_log_compare_pairwise_gate_status=pass`
- `linux_vulkan_render_log_compare_argb_source_gate_status=pass`
- `linux_vulkan_render_log_compare_renderdoc_gate_status=fail`
- `linux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC`
- `linux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=missing`
- `linux_vulkan_render_log_compare_renderdoc_chrome_reason=chromium-gpu-process-crashed-under-renderdoc`
- `linux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=missing`
- `linux_vulkan_render_log_compare_renderdoc_electron_reason=missing-rdc`

Authoritative generated env:
`build/linux-vulkan-render-log-compare-20260628-focused/evidence.env`.
