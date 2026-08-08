# GUI Showcase 4K/8K 200 FPS Evidence - 2026-06-28

## Scope

This report records a current-source retained GUI showcase performance refresh
for the GUI/web/2D hardening lane. It proves the native alias showcase producer
still meets the 4K 200 FPS target and the 8K retained target on this Linux host
without interpreter fallback. It does not prove the remaining RenderDoc,
Vulkan, Metal, Electron, Chrome, or per-widget GPU gates.

This is retained static alias performance evidence: both rows use
`render_mode=retained-static-frame` and `redraw_frames=1`. Treat the numbers as
native self-hosted retained producer throughput with ARGB checksum readback, not
as proof of non-software GPU throughput, continuous dynamic 8K repainting, or a
non-cached Chrome/Electron/RenderDoc path.

## Commands

```sh
RESOLUTION=4k TIMEOUT_SECS=30 \
BUILD_DIR=build/widget-showcase-4k-200fps-current-20260628-refresh \
  sh scripts/check/check-widget-showcase-4k-200fps.shs

RESOLUTION=8k TIMEOUT_SECS=30 \
BUILD_DIR=build/widget-showcase-8k-perf-current-20260628-refresh \
  sh scripts/check/check-widget-showcase-4k-200fps.shs

GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-current-20260628-refresh/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-current-20260628-refresh/status.env \
BUILD_DIR=build/gui-renderdoc-feature-coverage-with-refresh \
REPORT_PATH=build/gui-renderdoc-feature-coverage-with-refresh/report.md \
  sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## 4K Row

- status: `pass`
- reason: `met-200fps`
- source_revision: `368c2ecc61ed`
- source_revision_status: `current`
- backend: `simple-retained-widget-showcase`
- resolution: `3840x2160`
- frames: `200`
- fps_x1000: `57438253`
- target_fps: `200`
- frame_p50_ns: `17410`
- frame_p95_ns: `17410`
- max_rss_kb: `131328`
- max_rss_budget_kb: `262144`
- rss_status: `pass`
- nonzero_pixels: `5458`
- checksum: `23357114226484`
- readback_mode: `argb-checksum`
- render_mode: `retained-static-frame`
- redraw_frames: `1`
- simple_bin: `release/x86_64-unknown-linux-gnu/simple`
- simple_bin_source: `self-hosted-release`
- simple_bin_status: `pass`
- native_build_mode: `aggressive-native`
- fallback_state: `none`
- alias_raw_rt_count: `0`
- alias_src: `build/widget-showcase-4k-200fps-current-20260628-refresh/widget_showcase_4k_perf.spl`

## 8K Row

- status: `pass`
- reason: `met-target-fps`
- source_revision: `368c2ecc61ed`
- source_revision_status: `current`
- backend: `simple-retained-widget-showcase`
- resolution: `7680x4320`
- frames: `200`
- fps_x1000: `13652809`
- target_fps: `200`
- frame_p50_ns: `73245`
- frame_p95_ns: `73245`
- max_rss_kb: `520192`
- max_rss_budget_kb: `750000`
- rss_status: `pass`
- nonzero_pixels: `203`
- checksum: `869060580878`
- readback_mode: `argb-checksum`
- render_mode: `retained-static-frame`
- redraw_frames: `1`
- simple_bin: `release/x86_64-unknown-linux-gnu/simple`
- simple_bin_source: `self-hosted-release`
- simple_bin_status: `pass`
- native_build_mode: `aggressive-native`
- fallback_state: `none`
- alias_raw_rt_count: `0`
- alias_src: `build/widget-showcase-8k-perf-current-20260628-refresh/widget_showcase_8k_perf.spl`

## Aggregate Result

- `gui_showcase_4k_200fps_status=pass`
- `gui_showcase_4k_200fps_source_revision_status=current`
- `gui_showcase_4k_200fps_backend=simple-retained-widget-showcase`
- `gui_showcase_4k_200fps_readback_mode=argb-checksum`
- `gui_showcase_8k_perf_status=pass`
- `gui_showcase_8k_perf_source_revision_status=current`
- `gui_showcase_8k_perf_backend=simple-retained-widget-showcase`
- `gui_showcase_8k_perf_readback_mode=argb-checksum`
- `gui_renderdoc_feature_coverage_status=incomplete`
- `gui_renderdoc_feature_coverage_reason=missing-electron-widget-renderdoc`
- `blocked_completion_gate_count=8`

The retained 4K/8K performance sub-goal is current for the source files named
by the perf wrapper. The full active goal remains incomplete until the platform
GPU evidence gates also pass, including Electron widget RenderDoc, Linux Vulkan
RenderDoc comparison, macOS Metal readback/render-log comparison, Windows D3D12
render-log comparison, and production GUI/Web renderer parity.
