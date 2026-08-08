# RenderDoc Electron HTML Refresh - 2026-06-28

## Scope

This report records a focused refresh of the Electron Chromium/Vulkan RenderDoc
HTML evidence used by the GUI/web/2D hardening lane. It does not claim Electron
RenderDoc completion; it replaces stale source evidence with current launch and
GPU-process diagnostics.

## Commands

```sh
RDOC_OUTPUT_DIR=build/renderdoc/electron-display-helper \
RDOC_HTML_PATH="$PWD/test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html" \
RDOC_CAPTURE_TIMEOUT_SECS=30 \
  scripts/tool/renderdoc-evidence.shs capture-electron-html

RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/electron-display-helper/electron-html/evidence.env \
BUILD_DIR=build/renderdoc/electron-html-gate-refresh \
REPORT_PATH=build/renderdoc/electron-html-gate-refresh/report.md \
  sh scripts/check/check-renderdoc-electron-html-gate.shs
```

## Result

- `rdoc_electron_html_gate_status=fail`
- `rdoc_electron_html_gate_reason=missing-rdc`
- `rdoc_electron_html_gate_argb_status=pass`
- `rdoc_electron_html_gate_argb_nonblank_pixel_count=403594`
- `rdoc_electron_html_gate_launch_exit_code=0`
- `rdoc_electron_html_gate_launch_timed_out=false`
- `rdoc_electron_html_gate_launch_metadata_status=pass`
- `rdoc_electron_html_gate_source_contract_status=pass`
- `rdoc_electron_html_gate_gpu_process_exit_status=fail`
- `rdoc_electron_html_gate_gpu_process_exit_count=6`
- `rdoc_electron_html_gate_gpu_process_exit_codes=139`

The refreshed aggregate at
`build/gui-renderdoc-feature-coverage-with-refresh/evidence.env` now reports
`electron_renderdoc_gate_launch_metadata_status=pass` and
`electron_renderdoc_gate_source_contract_status=pass`. The remaining Electron
blocker is the missing `.rdc` artifact caused by Chromium GPU-process exits
under RenderDoc, not stale launch metadata.
