# GUI/Web/2D Vulkan Electron ARGB Evidence

- status: partial pass
- direct run env: `build/gui-web-2d-vulkan-env-run-electron/evidence.env`
- aggregate env: `build/gui-renderdoc-with-electron-run/evidence.env`
- browser backing env: `build/gui-web-2d-vulkan-browser-backing-electron/evidence.env`
- host: Linux x86_64
- Vulkan device: `llvmpipe (LLVM 20.1.2, 256 bits)`

## Passed Evidence

After installing the local Electron package with `npm ci` in
`tools/electron-shell`, the canonical direct-run wrapper produced nonblank ARGB
artifacts for Electron Chromium, Chrome, and Simple Vulkan at `1280x720`.

```text
gui_web_2d_vulkan_electron_argb_status=pass
gui_web_2d_vulkan_chrome_argb_status=pass
gui_web_2d_vulkan_simple_argb_status=pass
gui_web_2d_vulkan_pixel_comparison_status=pass
gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff
gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass
gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass
gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass
```

The aggregate gate also reports the retained 8k showcase row as passing the
200-frame target:

```text
gui_showcase_8k_perf_status=pass
gui_showcase_8k_perf_reason=met-target-fps
gui_showcase_8k_perf_frames=200
gui_showcase_8k_perf_fps_x1000=24218939
gui_showcase_8k_perf_target_fps=200
gui_showcase_8k_perf_rss_status=pass
```

## Remaining Blockers

Focused browser backing is still not complete on this host. Chrome reports
Vulkan-backed, but Electron lacks hardware Vulkan proof:

```text
gui_web_2d_vulkan_chrome_browser_backing_status=pass
gui_web_2d_vulkan_electron_browser_backing_status=fail
gui_web_2d_vulkan_electron_browser_backing_reason=electron-vulkan-hardware-missing
gui_web_2d_vulkan_browser_backing_status=fail
```

The overall aggregate remains incomplete because RenderDoc is not installed on
this host and production GUI/web parity evidence is absent:

```text
gui_renderdoc_feature_coverage_status=incomplete
gui_renderdoc_feature_coverage_reason=missing-simple-widget-renderdoc
renderdoc_goal_status=fail
renderdoc_goal_reason=missing-source-evidence
production_gui_web_renderer_parity_core_status=fail
production_gui_web_renderer_parity_core_reason=missing-production-parity-evidence
```

Do not mark the lane complete from this report alone. It proves Electron ARGB
pixel parity with Chrome and Simple Vulkan, not Electron Vulkan-backed browser
rendering or RenderDoc `.rdc` capture readiness.
