# GUI Showcase 4K/8K Retained Perf Evidence

Date: 2026-06-26

This report records fresh retained static-frame widget showcase performance rows
after hardening `scripts/check/check-widget-showcase-4k-200fps.shs` to resolve a
usable Simple launcher before the legacy Rust target and to emit
`*_simple_bin_source`.

## Commands

```sh
ALLOW_PATH_SIMPLE_BIN=1 \
BUILD_DIR=build/widget-showcase-4k-200fps-current-next \
TIMEOUT_SECS=60 \
sh scripts/check/check-widget-showcase-4k-200fps.shs

ALLOW_PATH_SIMPLE_BIN=1 \
RESOLUTION=8k \
BUILD_DIR=build/widget-showcase-8k-perf-current-next \
TIMEOUT_SECS=90 \
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
| fps_x1000 | 50025012 |
| frame_p50_ns | 19990 |
| frame_p95_ns | 19990 |
| target_fps | 200 |
| max_rss_kb | 131328 |
| max_rss_budget_kb | 262144 |
| rss_status | pass |
| nonzero_pixels | 5458 |
| checksum | 23357114226484 |
| render_mode | retained-static-frame |
| redraw_frames | 1 |
| source_revision | 2491f774049d |
| simple_bin | /home/ormastes/.local/bin/simple |
| simple_bin_source | path-opt-in |
| native_build_mode | aggressive-native |
| fallback_state | none |
| native_bin | build/widget-showcase-4k-200fps-current-next/widget_showcase_gui_perf |
| status_env | build/widget-showcase-4k-200fps-current-next/status.env |

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
| fps_x1000 | 13452613 |
| frame_p50_ns | 74335 |
| frame_p95_ns | 74335 |
| target_fps | 200 |
| max_rss_kb | 519936 |
| max_rss_budget_kb | 750000 |
| rss_status | pass |
| nonzero_pixels | 203 |
| checksum | 869060580878 |
| render_mode | retained-static-frame |
| redraw_frames | 1 |
| source_revision | 2491f774049d |
| simple_bin | /home/ormastes/.local/bin/simple |
| simple_bin_source | path-opt-in |
| native_build_mode | aggressive-native |
| fallback_state | none |
| native_bin | build/widget-showcase-8k-perf-current-next/widget_showcase_gui_perf |
| status_env | build/widget-showcase-8k-perf-current-next/status.env |

## Boundary

These rows prove retained static-frame 4K/8K showcase throughput, RSS budget,
native artifact provenance, and readback checksum/nonblank evidence for this
host. They do not prove live redraw throughput or native RenderDoc/PIX/GPU
debugger capture; those remain under the platform render-log and browser-backed
rendering gates.
