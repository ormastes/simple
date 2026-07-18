# GUI Showcase 4K/8K Retained Perf Refresh - 2026-06-27

## Summary

Fresh retained widget-showcase performance rows pass for the current showcase
source revision `56a1985b1d38`. The aggregate accepted both rows with
`*_source_revision_status=current`.

This proves retained static-frame 4K/8K throughput, RSS budget, ELF native
artifact provenance, checksum/readback evidence, and fallback state for this
host. It does not prove RenderDoc, Metal, D3D12, browser `.rdc`, live redraw
throughput, production parity, or full CSS coverage.

## Commands

```sh
ALLOW_PATH_SIMPLE_BIN=1 \
BUILD_DIR=build/widget-showcase-4k-200fps-current-2026-06-27-refresh \
TIMEOUT_SECS=60 \
sh scripts/check/check-widget-showcase-4k-200fps.shs

ALLOW_PATH_SIMPLE_BIN=1 \
RESOLUTION=8k \
BUILD_DIR=build/widget-showcase-8k-perf-current-2026-06-27-refresh \
TIMEOUT_SECS=90 \
sh scripts/check/check-widget-showcase-4k-200fps.shs
```

Aggregate perf-row check:

```sh
GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-current-2026-06-27-refresh/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-current-2026-06-27-refresh/status.env \
BUILD_DIR=build/gui-renderdoc-current-2026-06-27-perf-refresh \
REPORT_PATH=build/gui-renderdoc-current-2026-06-27-perf-refresh/report.md \
GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/gui-renderdoc-current-2026-06-27-perf-refresh-cache \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## 4K Row

| Field | Value |
| --- | --- |
| status | pass |
| reason | met-200fps |
| width x height | 3840 x 2160 |
| pixels | 8294400 |
| frames | 200 |
| fps_x1000 | 58055152 |
| frame_p50_ns | 17225 |
| frame_p95_ns | 17225 |
| target_fps | 200 |
| max_rss_kb | 131328 |
| max_rss_budget_kb | 262144 |
| rss_status | pass |
| nonzero_pixels | 5458 |
| checksum | 23357114226484 |
| render_mode | retained-static-frame |
| redraw_frames | 1 |
| source_revision | 56a1985b1d38 |
| source_revision_status | current |
| simple_bin_source | path-opt-in |
| native_bin_format_status | pass |
| fallback_state | none |
| log_file_status | pass |
| time_log_file_status | pass |

## 8K Row

| Field | Value |
| --- | --- |
| status | pass |
| reason | met-target-fps |
| width x height | 7680 x 4320 |
| pixels | 33177600 |
| frames | 200 |
| fps_x1000 | 13738150 |
| frame_p50_ns | 72790 |
| frame_p95_ns | 72790 |
| target_fps | 200 |
| max_rss_kb | 520192 |
| max_rss_budget_kb | 750000 |
| rss_status | pass |
| nonzero_pixels | 203 |
| checksum | 869060580878 |
| render_mode | retained-static-frame |
| redraw_frames | 1 |
| source_revision | 56a1985b1d38 |
| source_revision_status | current |
| simple_bin_source | path-opt-in |
| native_bin_format_status | pass |
| fallback_state | none |
| log_file_status | pass |
| time_log_file_status | pass |

## Aggregate Boundary

The aggregate status remains `incomplete` because this run intentionally fed
only perf evidence and did not provide the platform/browser/RenderDoc parity
envs. Remaining blockers include RenderDoc `.rdc` proof, native Linux/macOS/
Windows render-log comparison, production font/Metal/parity evidence, and full
CSS coverage.
