# GUI Web 2D Vulkan Direct Run Artifacts - 2026-06-27

## Summary

The focused `--run` evidence produced comparable Electron, Chrome, and Simple
ARGB artifacts on the current Linux Vulkan host. The aggregate accepted those
artifacts and removed the GUI/web/2D Vulkan comparison and pairwise pixel
comparison gates from `blocked_completion_gates`.

## Direct Run

```sh
SIMPLE_BIN=/home/ormastes/.local/bin/simple \
BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

Key rows:

- `gui_web_2d_vulkan_electron_argb_status=pass`
- `gui_web_2d_vulkan_electron_argb_width=1280`
- `gui_web_2d_vulkan_electron_argb_height=720`
- `gui_web_2d_vulkan_electron_argb_nonblank_pixel_count=403594`
- `gui_web_2d_vulkan_chrome_argb_status=pass`
- `gui_web_2d_vulkan_chrome_argb_width=1280`
- `gui_web_2d_vulkan_chrome_argb_height=720`
- `gui_web_2d_vulkan_chrome_argb_nonblank_pixel_count=403594`
- `gui_web_2d_vulkan_simple_status=pass`
- `gui_web_2d_vulkan_simple_reason=pass`
- `gui_web_2d_vulkan_simple_backend_name=vulkan`
- `gui_web_2d_vulkan_simple_argb_status=pass`
- `gui_web_2d_vulkan_simple_argb_width=1280`
- `gui_web_2d_vulkan_simple_argb_height=720`
- `gui_web_2d_vulkan_simple_argb_nonblank_pixel_count=403594`
- `gui_web_2d_vulkan_electron_chrome_diff_status=pass`
- `gui_web_2d_vulkan_electron_simple_diff_status=pass`
- `gui_web_2d_vulkan_chrome_simple_diff_status=pass`
- `gui_web_2d_vulkan_pixel_comparison_status=pass`
- `gui_web_2d_vulkan_pixel_comparison_reason=all-pairwise-diffs-pass`

## Aggregate

```sh
GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-current-2026-06-27/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-current-2026-06-27/status.env \
GUI_WEB_2D_VULKAN_ENV=build/gui-web-2d-vulkan-env-check-current/evidence.env \
GUI_WEB_2D_VULKAN_RUN_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-run-current/evidence.env \
GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-browser-backing-current/evidence.env \
BUILD_DIR=build/gui-renderdoc-current-2026-06-27-vulkan-run-artifacts \
REPORT_PATH=build/gui-renderdoc-current-2026-06-27-vulkan-run-artifacts/report.md \
GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/gui-renderdoc-current-2026-06-27-vulkan-run-artifacts-cache \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

Accepted aggregate rows:

- `gui_web_2d_vulkan_comparison_artifact_status=pass`
- `gui_web_2d_vulkan_comparison_artifact_reason=pass`
- `gui_web_2d_vulkan_pixel_comparison_status=pass`
- `gui_web_2d_vulkan_pixel_comparison_reason=pass`
- `gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff`
- `gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass`
- `gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass`
- `gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass`

Remaining blockers are RenderDoc `.rdc` capture, native platform render-log
comparison, production GUI/web parity, and full CSS coverage.
