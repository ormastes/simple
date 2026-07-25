# GUI Showcase Retained Performance Evidence - 2026-06-25

## Scope

This report records retained-mode GUI showcase performance evidence generated
on the current Linux host. It proves the retained static-frame showcase path,
not full Vulkan/Metal/Direct3D RenderDoc completion.

## Commands

```sh
RESOLUTION=4k BUILD_DIR=build/widget-showcase-4k-200fps-current TIMEOUT_SECS=30 \
  sh scripts/check/check-widget-showcase-4k-200fps.shs

RESOLUTION=8k BUILD_DIR=build/widget-showcase-8k-perf-current TIMEOUT_SECS=30 \
  sh scripts/check/check-widget-showcase-4k-200fps.shs

GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-current/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-current/status.env \
BUILD_DIR=build/gui-renderdoc-feature-coverage-showcase-current \
REPORT_PATH=build/gui-renderdoc-feature-coverage-showcase-current/report.md \
  sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true
```

## 4K Retained Row

- Status: `pass`
- Reason: `met-200fps`
- Viewport: `3840x2160`
- Pixels: `8294400`
- Frames: `200`
- FPS x1000: `54377379`
- Target FPS: `200`
- RSS: `131328 / 262144 KiB`
- RSS status: `pass`
- Nonzero pixels: `5458`
- Checksum: `23357114226484`
- Render mode: `retained-static-frame`
- Redraw frames: `1`
- Probe function: `run_4k_perf_probe`
- Probe prefix: `gui_showcase_4k_perf`
- Perf env flag: `SHOWCASE_4K_PERF`

## 8K Retained Row

- Status: `pass`
- Reason: `met-target-fps`
- Viewport: `7680x4320`
- Pixels: `33177600`
- Frames: `200`
- FPS x1000: `22750540`
- Target FPS: `200`
- RSS: `520192 / 750000 KiB`
- RSS status: `pass`
- Nonzero pixels: `203`
- Checksum: `869060580878`
- Render mode: `retained-static-frame`
- Redraw frames: `1`
- Probe function: `run_8k_perf_probe`
- Probe prefix: `gui_showcase_8k_perf`
- Perf env flag: `SHOWCASE_8K_PERF`

## Aggregate Status

The aggregate wrapper forwards both rows as `pass` with log and time-log file
status `pass`.

Remaining blockers are outside this retained perf proof: Simple/Electron/Chrome
RenderDoc `.rdc` lanes, browser Vulkan-backed proof, native render-log platform
matrix, production GUI/web parity evidence, and full CSS rendering coverage.
