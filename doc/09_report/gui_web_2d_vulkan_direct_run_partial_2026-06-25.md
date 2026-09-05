# GUI/Web/2D Vulkan Direct Run Partial Evidence

- status: incomplete
- reason: electron-argb-missing
- direct run env: `build/gui-web-2d-vulkan-env-run-goal-continue/evidence.env`
- aggregate env: `build/gui-renderdoc-with-run-goal-after-fix/evidence.env`
- Chrome ARGB: pass, `1280x720`, nonblank `403594`
- Simple Vulkan ARGB: pass, `1280x720`, nonblank `403594`
- Chrome/Simple pairwise diff: pass, mismatch count `0`
- Electron ARGB: unavailable, reason `missing-electron`
- aggregate pixel status: incomplete
- aggregate pixel mode: `artifact-only-no-pairwise-diff`

## Evidence

The canonical direct-run wrapper produced Chrome and Simple artifacts that match
pixel-for-pixel on this Linux host. Electron was not available, so the aggregate
now keeps the comparison incomplete instead of reporting a false mismatch:

```text
gui_web_2d_vulkan_pixel_comparison_status=incomplete
gui_web_2d_vulkan_pixel_comparison_reason=comparison-artifacts-incomplete;electron-chrome-diff-unavailable;electron-simple-diff-unavailable
gui_web_2d_vulkan_pixel_comparison_mode=artifact-only-no-pairwise-diff
gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass
```

Completion still requires Electron Chromium ARGB evidence, focused browser
Vulkan backing proof, RenderDoc `.rdc` captures, and production GUI/web parity.
