# GUI Showcase 4K/8K Aggregate Gate Evidence

Date: 2026-06-25

This report records the aggregate gate now consuming both retained showcase
performance rows:

```sh
SIMPLE_BIN=/home/ormastes/.local/bin/simple \
TIMEOUT_SECS=30 \
BUILD_DIR=build/widget-showcase-4k-200fps-goal \
sh scripts/check/check-widget-showcase-4k-200fps.shs

SIMPLE_BIN=/home/ormastes/.local/bin/simple \
RESOLUTION=8k \
TIMEOUT_SECS=60 \
BUILD_DIR=build/widget-showcase-8k-perf-goal \
sh scripts/check/check-widget-showcase-4k-200fps.shs

GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-goal/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-goal/status.env \
BUILD_DIR=build/gui-renderdoc-with-4k-8k-perf-goal \
REPORT_PATH=build/gui-renderdoc-with-4k-8k-perf-goal/report.md \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## 4K Row

- status: `pass`
- reason: `met-200fps`
- geometry: `3840x2160`, pixels `8294400`
- frames: `200`
- fps_x1000: `56689342`
- target_fps: `200`
- checksum: `23357114226484`
- nonzero_pixels: `5458`
- render_mode: `retained-static-frame`
- redraw_frames: `1`
- max_rss_kb: `131072`
- max_rss_budget_kb: `262144`
- rss_status: `pass`
- source_revision: `51ba1025b4d9`
- simple_bin: `src/compiler_rust/target/release/simple`
- native_build_mode: `aggressive-native`
- fallback_state: `none`

## 8K Row

- status: `pass`
- reason: `met-target-fps`
- geometry: `7680x4320`, pixels `33177600`
- frames: `200`
- fps_x1000: `22711787`
- target_fps: `200`
- checksum: `869060580878`
- nonzero_pixels: `203`
- render_mode: `retained-static-frame`
- redraw_frames: `1`
- max_rss_kb: `520192`
- max_rss_budget_kb: `750000`
- rss_status: `pass`
- source_revision: `51ba1025b4d9`
- simple_bin: `src/compiler_rust/target/release/simple`
- native_build_mode: `aggressive-native`
- fallback_state: `none`

The aggregate now forwards passing `gui_showcase_4k_200fps_*` and
`gui_showcase_8k_perf_*` fields. Completion remains blocked by the non-perf
RenderDoc/browser-backing/production-parity/full-CSS gates.
