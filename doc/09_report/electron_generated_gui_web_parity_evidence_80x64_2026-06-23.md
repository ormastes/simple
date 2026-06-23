# Electron Generated GUI Web Parity 80x64 Evidence

- status: unavailable
- reason: simple-render-failed
- command: `SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple ELECTRON_BITMAP_WIDTH=80 ELECTRON_BITMAP_HEIGHT=64 ELECTRON_BITMAP_TIMEOUT_SECS=20 BUILD_DIR=build/electron_generated_gui_web_parity_evidence_80x64_retry REPORT_PATH=doc/09_report/electron_generated_gui_web_parity_evidence_80x64_2026-06-23.md sh scripts/check/check-electron-generated-gui-web-parity-evidence.shs`
- dependency status: Electron installed under `tools/electron-shell/node_modules`
- scene: generated-gui-widget-html
- width: 80
- height: 64

## Raw Evidence

- electron_generated_gui_web_status=unavailable
- electron_generated_gui_web_reason=simple-render-failed
- electron_generated_gui_web_scene=generated-gui-widget-html
- electron_generated_gui_web_width=80
- electron_generated_gui_web_height=64

## Blocker

The previous `missing-electron-dependency` blocker is cleared locally by
installing `tools/electron-shell` dependencies. The focused 80x64 run now reaches
the Simple render step and fails there. `simple.out` ends with
`error: example timed out after 60s: examples/06_io/ui/generated_gui_web_parity_expected.spl`
and repeated `CODEGEN-AMBIGUOUS-METHOD` diagnostics for `Engine2D` draw calls.
