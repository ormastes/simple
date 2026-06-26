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
  sh scripts/check/check-widget-showcase-4k-200fps.shs

RESOLUTION=8k BUILD_DIR=build/widget-showcase-8k-perf TIMEOUT_SECS=30 \
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
- Source revision: `b5c9308f9351`
- Current source revision: `b5c9308f9351`
- Source revision status: `current`
- Strict source requirement: `1`

## 4K Retained Row

- Status: `pass`
- Reason: `met-200fps`
- Viewport: `3840x2160`
- Pixels: `8294400`
- Frames: `200`
- FPS x1000: `51242633`
- Target FPS: `200`
- Frame avg/p50/p95 ns: `19515 / 19515 / 19515`
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
- FPS x1000: `21097046`
- Target FPS: `200`
- Frame avg/p50/p95 ns: `47400 / 47400 / 47400`
- RSS: `520192 / 750000 KiB`
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
