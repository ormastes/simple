# GUI Showcase Retained Performance Evidence - 2026-06-26

## Scope

This report records retained-mode GUI showcase performance evidence generated on
the Linux host. It proves the retained static-frame 4K and 8K showcase paths
with native aggressive builds. It does not prove Chrome/Electron RenderDoc
capture, macOS Metal, Windows D3D12, production GUI/web parity, or full CSS
completion.

## Commands

```sh
RESOLUTION=4k BUILD_DIR=build/widget-showcase-4k-200fps TIMEOUT_SECS=30 \
SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple \
  sh scripts/check/check-widget-showcase-4k-200fps.shs

RESOLUTION=8k BUILD_DIR=build/widget-showcase-8k-perf TIMEOUT_SECS=30 \
SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple \
  sh scripts/check/check-widget-showcase-4k-200fps.shs

GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/gui-renderdoc-feature-coverage-static-cache \
BUILD_DIR=build/gui-renderdoc-feature-coverage-status \
REPORT_PATH=build/gui-renderdoc-feature-coverage-status/report.md \
  sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true
```

## Source Freshness

- Revision kind: `content-sha256`
- Revision files: `scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl`
- Source revision: `612bdcefecfc`
- Current source revision: `612bdcefecfc`
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
- FPS x1000: `48076923`
- Target FPS: `200`
- Frame avg/p50/p95 ns: `20800 / 20800 / 20800`
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
- FPS x1000: `10712946`
- Target FPS: `200`
- Frame avg/p50/p95 ns: `93345 / 93345 / 93345`
- RSS: `519680 / 750000 KiB`
- RSS status: `pass`
- Nonzero pixels: `203`
- Checksum: `869060580878`
- Render mode: `retained-static-frame`
- Redraw frames: `1`
- Native mode: `aggressive-native`
- Fallback: `none`

## Remaining Blockers

The aggregate remains incomplete because Chrome and Electron RenderDoc `.rdc`
artifacts are missing, the native render-log matrix still lacks macOS Metal and
Windows D3D12 evidence, production GUI/web parity is incomplete, and full CSS
coverage is not yet complete.
