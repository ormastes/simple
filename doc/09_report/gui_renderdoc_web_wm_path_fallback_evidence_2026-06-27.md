# GUI RenderDoc Web WM Path Fallback Evidence - 2026-06-27

## Summary

The Web WM modern shell evidence gate now passes through the aggregate on the
current Linux host by using the aggregate-owned `ALLOW_PATH_SIMPLE_CMD=1`
fallback. Direct wrapper runs remain conservative unless the opt-in is set.

## Command

```sh
GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-current-2026-06-27/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-current-2026-06-27/status.env \
GUI_WEB_2D_VULKAN_ENV=build/gui-web-2d-vulkan-env-check-current/evidence.env \
GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-browser-backing-current/evidence.env \
BUILD_DIR=build/gui-renderdoc-current-2026-06-27-webwm-path-fallback \
REPORT_PATH=build/gui-renderdoc-current-2026-06-27-webwm-path-fallback/report.md \
GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/gui-renderdoc-current-2026-06-27-webwm-path-fallback-cache \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## Evidence Rows

- `gui_renderdoc_feature_coverage_status=incomplete`
- `web_wm_modern_shell_evidence_source=nested-run`
- `web_wm_modern_shell_evidence_status=pass`
- `web_wm_modern_shell_evidence_reason=pass`
- `web_wm_modern_shell_evidence_html_file_status=pass`
- `web_wm_modern_shell_evidence_argb_file_status=pass`
- `web_wm_modern_shell_evidence_png_file_status=pass`
- `web_wm_modern_shell_evidence_audit_file_status=pass`
- `web_wm_modern_shell_evidence_interaction_file_status=pass`
- `web_wm_modern_shell_evidence_interaction_png_file_status=pass`
- `web_wm_modern_shell_evidence_interaction_log_file_status=pass`
- `web_wm_modern_shell_evidence_bitmap_nonblank_status=pass`
- `web_wm_modern_shell_evidence_audit_pass=pass`
- `web_wm_modern_shell_evidence_interaction_pass=pass`
- `web_wm_modern_shell_evidence_interaction_focus=pass`
- `web_wm_modern_shell_evidence_interaction_keyboard=pass`
- `web_wm_modern_shell_evidence_interaction_input=pass`
- `web_wm_modern_shell_evidence_interaction_pointer=pass`

## Remaining Aggregate Blockers

- Simple Vulkan Engine2D RenderDoc `.rdc` with `RDOC` magic.
- Original Chrome-on-Vulkan RenderDoc `.rdc` with `RDOC` magic.
- Electron Chromium-on-Vulkan RenderDoc `.rdc` with nonblank ARGB render proof.
- Simple GUI widget RenderDoc `.rdc` on Vulkan Engine2D.
- Electron Chromium-on-Vulkan widget RenderDoc `.rdc` with nonblank ARGB proof.
- GUI/web/2D Vulkan comparison artifacts for Electron, Chrome, and Simple.
- Simple Vulkan Engine2D clear/rect readback parity evidence.
- Electron, Chrome, and Simple GUI/web/2D Vulkan pairwise pixel comparison.
- Native render-log comparison for Linux Vulkan, macOS Metal, and Windows D3D12.
- Production GUI/web font offload readback evidence.
- Production GUI/web raw Metal readback evidence.
- Production GUI/web parity evidence with live Tauri and Chrome captures.
- Full CSS specification rendering coverage beyond implemented Simple Web subset.
