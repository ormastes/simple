# GUI Showcase 4K/8K Retained Perf Evidence

Date: 2026-06-25

This report records the retained static-frame widget showcase performance rows
for the active GUI/web/2D hardening lane. The probe draws once, presents the
retained frame repeatedly, then validates full-size readback geometry,
nonzero pixels, checksum, retained render mode, and redraw count.

## Commands

```sh
SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple \
BUILD_DIR=build/widget-showcase-4k-200fps-current \
TIMEOUT_SECS=30 \
sh scripts/check/check-widget-showcase-4k-200fps.shs

SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple \
RESOLUTION=8k \
BUILD_DIR=build/widget-showcase-8k-perf-current \
TIMEOUT_SECS=30 \
sh scripts/check/check-widget-showcase-4k-200fps.shs
```

## 4K Row

| Field | Value |
| --- | --- |
| status | pass |
| reason | met-200fps |
| resolution | 4k |
| width | 3840 |
| height | 2160 |
| pixels | 8294400 |
| frames | 200 |
| fps_x1000 | 54377379 |
| target_fps | 200 |
| max_rss_kb | 131328 |
| max_rss_budget_kb | 262144 |
| rss_status | pass |
| nonzero_pixels | 5458 |
| checksum | 23357114226484 |
| render_mode | retained-static-frame |
| redraw_frames | 1 |
| source_revision | 61a23c540971 |
| simple_bin | src/compiler_rust/target/release/simple |
| use_native | 1 |
| native_build_mode | aggressive-native |
| fallback_state | none |
| native_bin | build/widget-showcase-4k-200fps-current/widget_showcase_gui_perf |
| status_env | build/widget-showcase-4k-200fps-current/status.env |

## 8K Row

| Field | Value |
| --- | --- |
| status | pass |
| reason | met-target-fps |
| resolution | 8k |
| width | 7680 |
| height | 4320 |
| pixels | 33177600 |
| frames | 200 |
| fps_x1000 | 22750540 |
| target_fps | 200 |
| max_rss_kb | 520192 |
| max_rss_budget_kb | 750000 |
| rss_status | pass |
| nonzero_pixels | 203 |
| checksum | 869060580878 |
| render_mode | retained-static-frame |
| redraw_frames | 1 |
| source_revision | 61a23c540971 |
| simple_bin | src/compiler_rust/target/release/simple |
| use_native | 1 |
| native_build_mode | aggressive-native |
| fallback_state | none |
| native_bin | build/widget-showcase-8k-perf-current/widget_showcase_gui_perf |
| status_env | build/widget-showcase-8k-perf-current/status.env |

## Remaining Non-Perf Blockers

This report proves the 4K and 8K retained showcase perf rows. It does not prove
Vulkan/Metal/D3D12 browser backing, RenderDoc/PIX/GPU-debugger capture, or
production GUI/web renderer parity. Those remain governed by the platform
render-log gates and the GUI RenderDoc feature coverage aggregate.
