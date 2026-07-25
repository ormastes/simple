# GUI Showcase Retained Performance Evidence - 2026-06-26

## Scope

This report records retained-mode GUI showcase performance evidence generated on
the Linux host. It proves the retained static-frame 4K and 8K showcase paths
with native aggressive builds. It does not prove Chrome/Electron RenderDoc
capture, macOS Metal, Windows D3D12, production GUI/web parity, or full CSS
completion.

## Commands

```sh
RESOLUTION=4k BUILD_DIR=build/widget-showcase-4k-200fps TIMEOUT_SECS=120 \
SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple \
  sh scripts/check/check-widget-showcase-4k-200fps.shs

RESOLUTION=4k BUILD_DIR=build/widget-showcase-4k-200fps-live-20260626 TIMEOUT_SECS=30 \
SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple \
  sh scripts/check/check-widget-showcase-4k-200fps.shs

RESOLUTION=8k BUILD_DIR=build/widget-showcase-8k-perf TIMEOUT_SECS=180 \
SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple \
  sh scripts/check/check-widget-showcase-4k-200fps.shs

RESOLUTION=8k BUILD_DIR=build/widget-showcase-8k-perf-live-20260626 TIMEOUT_SECS=60 \
SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple \
  sh scripts/check/check-widget-showcase-4k-200fps.shs

GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf/status.env \
GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/gui-renderdoc-feature-coverage-static-cache \
BUILD_DIR=build/gui-renderdoc-feature-coverage-status \
REPORT_PATH=build/gui-renderdoc-feature-coverage-status/report.md \
  sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true

GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-live-20260626/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-live-20260626/status.env \
GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/gui-renderdoc-feature-coverage-static-cache \
BUILD_DIR=build/gui-renderdoc-feature-coverage-status-live-20260626 \
REPORT_PATH=build/gui-renderdoc-feature-coverage-status-live-20260626/report.md \
  sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true
```

## Source Freshness

- Revision kind: `content-sha256`
- Revision files: `scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl`
- Source revision: `1f4d4bad665f`
- Current source revision: `1f4d4bad665f`
- Source revision status: `current`
- Strict source requirement: `1`

## Implementation Note

The showcase app now routes environment reads through the existing
`std.nogc_sync_mut.io.env_ops.env_get` facade and handles
`SHOWCASE_8K_PERF=1` directly. The 8K probe reports the same 200 frame count
that the wrapper validates, so the FPS row is no longer inflated by a shorter
internal probe loop.

## 4K Retained Row

- Status: `pass`
- Reason: `met-200fps`
- Viewport: `3840x2160`
- Pixels: `8294400`
- Frames: `200`
- FPS x1000: `54421768`
- Target FPS: `200`
- Frame avg/p50/p95 ns: `18375 / 18375 / 18375`
- Frame elapsed ns: `3675000`
- Frame elapsed status: `pass`
- RSS: `131328 / 262144 KiB`
- RSS status: `pass`
- Nonzero pixels: `5458`
- Checksum: `23357114226484`
- Render mode: `retained-static-frame`
- Redraw frames: `1`
- Native mode: `aggressive-native`
- Fallback: `none`

## 8K Retained Row

- Status: `pass`
- Reason: `met-target-fps`
- Viewport: `7680x4320`
- Pixels: `33177600`
- Frames: `200`
- FPS x1000: `13609145`
- Target FPS: `200`
- Frame avg/p50/p95 ns: `73480 / 73480 / 73480`
- Frame elapsed ns: `14696000`
- Frame elapsed status: `pass`
- RSS: `520192 / 750000 KiB`
- RSS status: `pass`
- Nonzero pixels: `203`
- Checksum: `869060580878`
- Render mode: `retained-static-frame`
- Redraw frames: `1`
- Native mode: `aggressive-native`
- Fallback: `none`

## Remaining Blockers

With both retained perf env files supplied, the aggregate reports
`gui_showcase_4k_200fps_status=pass`,
`gui_showcase_8k_perf_status=pass`, and
`blocked_completion_gate_count=15`.

The aggregate remains incomplete because Chrome and Electron RenderDoc `.rdc`
artifacts are missing, GUI widget RenderDoc captures are missing, Vulkan
comparison and browser backing evidence are incomplete, the native render-log
matrix still lacks Linux Vulkan, macOS Metal, and Windows D3D12 completion
evidence, production GUI/web parity is incomplete, and full CSS coverage is not
yet complete.
