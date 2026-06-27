# GUI Showcase 4K/8K 200 FPS Evidence - 2026-06-27

## Scope

This report records a bounded retained-frame GUI showcase performance run for
the active GUI/web/2D hardening lane. It proves the native retained showcase
producer and aggregate accepted fresh 4K and 8K rows on this Linux host. It
does not prove the remaining RenderDoc, Vulkan, Metal, Electron, Chrome, or
per-widget GPU gates.

## Commands

```sh
RESOLUTION=4k TIMEOUT_SECS=20 BUILD_DIR=build/live-widget-showcase-4k-200fps \
  sh scripts/check/check-widget-showcase-4k-200fps.shs

RESOLUTION=8k TIMEOUT_SECS=20 BUILD_DIR=build/live-widget-showcase-8k-perf \
  sh scripts/check/check-widget-showcase-4k-200fps.shs

GUI_SHOWCASE_4K_PERF_ENV=build/live-widget-showcase-4k-200fps/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/live-widget-showcase-8k-perf/status.env \
BUILD_DIR=build/live-widget-showcase-aggregate \
REPORT_PATH=build/live-widget-showcase-aggregate/report.md \
  sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## 4K Row

- status: `pass`
- reason: `met-200fps`
- resolution: `3840x2160`
- frames: `200`
- fps_x1000: `55865921`
- target_fps: `200`
- frame_avg_ns: `17900`
- frame_p50_ns: `17900`
- frame_p95_ns: `17900`
- max_rss_kb: `131328`
- max_rss_budget_kb: `262144`
- rss_status: `pass`
- nonzero_pixels: `5458`
- checksum: `23357114226484`
- render_mode: `retained-static-frame`
- redraw_frames: `1`
- simple_bin: `release/x86_64-unknown-linux-gnu/simple`
- simple_bin_source: `self-hosted-release`
- simple_bin_status: `pass`
- native_build_mode: `aggressive-native`
- fallback_state: `none`

## 8K Row

- status: `pass`
- reason: `met-target-fps`
- resolution: `7680x4320`
- frames: `200`
- fps_x1000: `15518311`
- target_fps: `200`
- frame_avg_ns: `64440`
- frame_p50_ns: `64440`
- frame_p95_ns: `64440`
- max_rss_kb: `520192`
- max_rss_budget_kb: `750000`
- rss_status: `pass`
- nonzero_pixels: `203`
- checksum: `869060580878`
- render_mode: `retained-static-frame`
- redraw_frames: `1`
- simple_bin: `release/x86_64-unknown-linux-gnu/simple`
- simple_bin_source: `self-hosted-release`
- simple_bin_status: `pass`
- native_build_mode: `aggressive-native`
- fallback_state: `none`

## Aggregate Result

- `gui_showcase_4k_200fps_status=pass`
- `gui_showcase_8k_perf_status=pass`
- `gui_renderdoc_feature_coverage_status=incomplete`
- `gui_widget_renderdoc_goal_status=incomplete`

The aggregate incompleteness is expected for this host run because the broader
RenderDoc/GPU widget gates were not provided with passing platform evidence.
This report is therefore valid only for the retained 4K/8K showcase performance
sub-goal.
