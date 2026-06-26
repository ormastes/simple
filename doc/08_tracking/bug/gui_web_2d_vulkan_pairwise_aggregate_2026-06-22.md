# GUI/Web/2D Vulkan Pairwise Aggregate Evidence

- Date: 2026-06-22
- Status: pass for pairwise pixels; browser/RenderDoc completion still blocked
- Gate: `scripts/setup/setup-gui-web-2d-vulkan-env.shs --run`
- Evidence: `build/gui-web-2d-vulkan-env/evidence.env`

## Current Evidence

Latest refresh on 2026-06-23 selects a same-repository PATH `simple` when the
linked worktree has no `bin/simple`. Electron, Chrome, and Simple ARGB capture
pass with zero pairwise mismatches:

```text
gui_web_2d_vulkan_simple_bin=/home/ormastes/.local/bin/simple
gui_web_2d_vulkan_simple_bin_selection_reason=default-missing-same-repo-path-fallback
gui_web_2d_vulkan_simple_status=pass
gui_web_2d_vulkan_simple_argb_exit_code=0
gui_web_2d_vulkan_simple_argb_status=pass
gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass
gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass
gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass
gui_web_2d_vulkan_comparison_artifact_status=pass
gui_web_2d_vulkan_comparison_artifact_reason=pass
gui_web_2d_vulkan_pixel_comparison_status=pass
gui_web_2d_vulkan_pixel_comparison_reason=all-pairwise-diffs-pass
gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff
gui_web_2d_vulkan_chrome_screenshot_file_status=missing
gui_web_2d_vulkan_chrome_argb_file_status=pass
gui_web_2d_vulkan_chrome_argb_viewport_match_status=pass
gui_web_2d_vulkan_chrome_argb_nonblank_status=pass
gui_web_2d_vulkan_browser_backing_status=fail
gui_web_2d_vulkan_browser_backing_reason=electron-vulkan-disabled_off;chrome-vulkan-backed
```

The stale checked-in `bin/simple_native` crash is tracked separately:
`doc/08_tracking/bug/gui_web_2d_vulkan_simple_native_crash_2026-06-23.md`.

Historical retained pass evidence:

```text
gui_web_2d_vulkan_loader_status=present
gui_web_2d_vulkan_device=llvmpipe (LLVM 20.1.2, 256 bits)
gui_web_2d_vulkan_electron_argb_status=pass
gui_web_2d_vulkan_electron_argb_path=build/gui-web-2d-vulkan-env/electron_argb.json
gui_web_2d_vulkan_chrome_argb_status=pass
gui_web_2d_vulkan_chrome_argb_proof=build/gui-web-2d-vulkan-env/chrome_argb_proof.json
gui_web_2d_vulkan_simple_status=pass
gui_web_2d_vulkan_simple_backend_name=vulkan
gui_web_2d_vulkan_browser_backing_mode=gpu-feature-status
gui_web_2d_vulkan_electron_browser_backing_status=fail
gui_web_2d_vulkan_electron_browser_backing_reason=electron-vulkan-disabled_off
gui_web_2d_vulkan_electron_browser_backing_vulkan=disabled_off
gui_web_2d_vulkan_electron_browser_backing_hardware_supports_vulkan=false
gui_web_2d_vulkan_chrome_browser_backing_status=pass
gui_web_2d_vulkan_chrome_browser_backing_reason=chrome-vulkan-backed
gui_web_2d_vulkan_browser_backing_status=fail
gui_web_2d_vulkan_browser_backing_reason=electron-vulkan-disabled_off;chrome-vulkan-backed
gui_web_2d_vulkan_simple_argb_status=pass
gui_web_2d_vulkan_simple_argb_nonblank_pixel_count=403594
gui_web_2d_vulkan_electron_chrome_diff_status=pass
gui_web_2d_vulkan_electron_chrome_mismatch_count=0
gui_web_2d_vulkan_electron_chrome_max_channel_delta=0
gui_web_2d_vulkan_electron_chrome_total_delta=0
gui_web_2d_vulkan_electron_chrome_bg_diff_count=0
gui_web_2d_vulkan_electron_chrome_text_diff_count=0
gui_web_2d_vulkan_electron_chrome_diff_bbox=none
gui_web_2d_vulkan_electron_chrome_diff_component_count=0
gui_web_2d_vulkan_electron_chrome_diff_top_components=
gui_web_2d_vulkan_electron_simple_diff_status=pass
gui_web_2d_vulkan_electron_simple_mismatch_count=0
gui_web_2d_vulkan_electron_simple_max_channel_delta=0
gui_web_2d_vulkan_electron_simple_total_delta=0
gui_web_2d_vulkan_electron_simple_bg_diff_count=0
gui_web_2d_vulkan_electron_simple_text_diff_count=0
gui_web_2d_vulkan_electron_simple_diff_bbox=none
gui_web_2d_vulkan_electron_simple_diff_component_count=0
gui_web_2d_vulkan_electron_simple_diff_top_components=
gui_web_2d_vulkan_chrome_simple_diff_status=pass
gui_web_2d_vulkan_chrome_simple_mismatch_count=0
gui_web_2d_vulkan_chrome_simple_max_channel_delta=0
gui_web_2d_vulkan_chrome_simple_total_delta=0
gui_web_2d_vulkan_chrome_simple_bg_diff_count=0
gui_web_2d_vulkan_chrome_simple_text_diff_count=0
gui_web_2d_vulkan_chrome_simple_diff_bbox=none
gui_web_2d_vulkan_chrome_simple_diff_component_count=0
gui_web_2d_vulkan_chrome_simple_diff_top_components=
gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass
gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass
gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass
gui_web_2d_vulkan_electron_simple_excess_over_browser_floor=0
gui_web_2d_vulkan_chrome_simple_excess_over_browser_floor=0
gui_web_2d_vulkan_simple_browser_floor_status=pass
gui_web_2d_vulkan_simple_browser_floor_reason=simple-has-no-excess-over-electron-chrome-drift
gui_web_2d_vulkan_pixel_comparison_status=pass
gui_web_2d_vulkan_pixel_comparison_reason=all-pairwise-diffs-pass
gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff
```

## Historical Notes

Earlier retained evidence showed Simple Vulkan Engine2D readback passing and
the Simple HTML ARGB renderer producing a full capture through Simple facades
instead of direct `rt_*` calls. That historical pass is no longer current on the
linked worktree until the 2026-06-23 Simple native crash above is fixed. Browser
backing also remains separate: Chrome had proved Vulkan backing through DevTools
GPU info, but Electron reported `vulkan=disabled_off` and
`hardwareSupportsVulkan=false`. The aggregate remains fail-closed until Simple
ARGB, pairwise comparison, and Electron browser backing all pass again.

## Cross-Platform Electron Backing Plan

This Linux/Xvfb host cannot complete the Electron-backed Vulkan proof with the
current Electron stack: Electron reports `vulkan=disabled_off` and direct/visible
launches hit the Xvfb/DRI3 `UnknownVizError` path. Finish the Electron lane on:

1. macOS with MoltenVK: run `scripts/setup/setup-gui-web-2d-vulkan-env.shs --check`
   and then `--run`; require Electron backing `pass` with Metal or MoltenVK GPU
   metadata.
2. Linux desktop with real DRI3/Wayland or Xorg GPU access, not Xvfb: run the
   same `--run` gate; require `hardwareSupportsVulkan=true` plus pixel parity
   `pass`.
3. If both fail, change the Electron proof backend instead of adding more
   Chromium flags on this host.

## 8K Showcase Status

The 8K showcase gate now separates retained-frame presentation timing from the
final readback/checksum proof. Saved evidence:

```text
gui_showcase_8k_perf_status=pass
gui_showcase_8k_perf_frame_elapsed_ns=8869000
gui_showcase_8k_perf_fps_x1000=13530273
gui_showcase_8k_perf_target_fps=200
gui_showcase_8k_perf_pixels=33177600
gui_showcase_8k_perf_checksum=894747485546
```

That is about 13,530 FPS for retained presentation at 7680x4320, with the
full 8K readback/checksum still verified after the frame loop. The process
elapsed row remains recorded separately as `gui_showcase_8k_perf_elapsed_ns`.

## When The Aggregate Fails

Use this same record as the blocker target when the aggregate reports either:

- `gui_web_2d_vulkan_comparison_artifact_status` is not `pass`
- `gui_web_2d_vulkan_pixel_comparison_status` is not `pass`

Artifact failures mean one of Electron, Chrome, or Simple lacks the required
ARGB/screenshot/evidence file. Pixel failures mean the pairwise ARGB diff lanes
did not all reach zero mismatch. Do not claim GUI/web/2D Vulkan parity until the
aggregate returns `gui_web_2d_vulkan_pixel_comparison_status=pass` with
`gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff`.

## Rejected Electron Backing Shortcuts

Do not repeat these without a different Electron/GPU host path:

- Extra Chromium flags
  `--ignore-gpu-blocklist --enable-gpu-rasterization --disable-software-rasterizer`
  still reported `vulkan=disabled_off`, `(gl=none,angle=none)`, and
  `hardwareSupportsVulkan=false`.
- Moving Vulkan switches into `app.commandLine.appendSwitch()` before
  `app.whenReady()` produced the same software-compositing state.
- A visible `BrowserWindow` and direct
  `tools/electron-shell/node_modules/electron/dist/electron` launcher both
  failed under Xvfb before ARGB output with `UnknownVizError` and
  `dri3 extension not supported`.

## 2026-06-22 Native Probe Crash Cause

The native Simple ARGB probe crashed or logged
`function not found: Engine2D.is_err` when the browser presenter routed
`cpu_simd` through `Engine2D.create_requested_backend()` and then called
`Result.is_err()`. In the native compiled path that Result can dispatch as the
wrapped `Engine2D`, so the method lookup is invalid. The session plan is to keep
software, `cpu`, and `cpu_simd` aliases on the direct `cpu_mirror` path, leaving
real GPU backend requests on the existing Engine2D path. Verification evidence:
native probe exit `0`, `Engine2D.is_err` stderr count `0`, JSON pixels `768`,
and GUI/Web/2D Vulkan pairwise mismatches all `0`.
