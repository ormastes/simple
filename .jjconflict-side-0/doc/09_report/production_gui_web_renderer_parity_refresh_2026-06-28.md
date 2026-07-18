# Production GUI/Web Renderer Parity Refresh - 2026-06-28

## Scope

This report records a focused headless refresh of the production GUI/Web
renderer parity gate for the GUI/web/2D hardening lane. It does not claim
production parity completion. It replaces missing aggregate production evidence
with a structured failing source.

## Commands

```sh
BUILD_ROOT=build/production_gui_web_renderer_parity_evidence_refresh \
REPORT_PATH=build/production_gui_web_renderer_parity_evidence_refresh/report.md \
PRODUCTION_GUI_WEB_RENDERER_PARITY_SUBCHECK_TIMEOUT_SECS=60 \
ELECTRON_BITMAP_TIMEOUT_SECS=20 \
CHROME_LAYOUT_TIMEOUT_SECS=30 \
  sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs

BUILD_DIR=build/production_gui_web_renderer_parity_evidence_refresh/layout_manifest \
REPORT_PATH=build/production_gui_web_renderer_parity_evidence_refresh/layout_manifest/report.md \
ELECTRON_BITMAP_TIMEOUT_SECS=20 \
ELECTRON_LAYOUT_MANIFEST_RESUME=1 \
  timeout 180 sh scripts/check/check-electron-simple-web-layout-manifest-evidence.shs
```

## Result

- `production_gui_web_renderer_parity_status=fail`
- `production_gui_web_renderer_parity_reason=electron-layout-manifest-failed`
- `production_gui_web_renderer_parity_matrix_status=pass`
- `production_gui_web_renderer_parity_backend_status=pass`
- `production_gui_web_renderer_parity_surface_manifest_status=fail`
- `production_gui_web_renderer_parity_font_offload_status=unavailable`
- `production_gui_web_renderer_parity_metal_readback_status=fail`
- `production_gui_web_renderer_parity_metal_render_log_status=skipped`

The first bounded wrapper run reached 5 Electron layout manifest cases before
the 60s subcheck timeout. A focused resume advanced the manifest evidence to 25
case rows. The resumed evidence still did not reach the final manifest summary,
and the derived strict counts are:

- `derived_case_count=25`
- `derived_pass_count=2`
- `derived_tracked_count=0`
- `derived_fail_count=23`

## First Layout Failures

- `css_box_matrix`: `paint-color-mismatch`, mismatch `124`
- `border_nested_matrix`: `paint-color-mismatch`, mismatch `779`
- `selector_inline_box_matrix`: `paint-color-mismatch`, mismatch `4023`
- `attribute_selector_box_matrix`: `paint-color-mismatch`, mismatch `3701`
- `pseudo_selector_matrix`: `paint-color-mismatch`, mismatch `3866`
- `padding_longhand_matrix`: `paint-color-mismatch`, mismatch `3362`

## Aggregate Effect

`build/gui-renderdoc-feature-coverage-with-refresh/evidence.env` now records a
structured production parity gate failure instead of a missing production parity
source:

- `production_gui_web_renderer_parity_gate_status=fail`
- `production_gui_web_renderer_parity_gate_reason=electron-layout-manifest-failed`
- `production_gui_web_renderer_parity_gate_layout_manifest_status=timeout`
- `production_gui_web_renderer_parity_gate_surface_manifest_status=fail`
- `production_gui_web_renderer_parity_gate_backend_status=pass`
- `production_gui_web_renderer_parity_gate_font_offload_status=unavailable`
- `production_gui_web_renderer_parity_gate_metal_readback_status=fail`
- `production_gui_web_renderer_parity_gate_event_routing_status=missing`

The remaining work is implementation and platform evidence, not merely a missing
wrapper invocation.
