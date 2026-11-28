# System & Unit Test Plan: Simple Web Engine Completion (`release/1.0.0`)

- **Date:** 2026-11-28
- **Target Branch:** `release/1.0.0`
- **Requirements:** `REQ-WEB-001`..`REQ-WEB-008`, `NFR-WEB-001`..`NFR-WEB-005`

## 1. Test Coverage Matrix

| Req ID | SSpec Test File | Key Real Assertions (No Placeholders) |
|---|---|---|
| `REQ-WEB-001` | `test/01_unit/browser_engine/float_paint_stacking_order_chrome159_spec.spl` + `test/01_unit/browser_engine/float_fractional_height_clear_chrome159_spec.spl` | Float box (`float:left`/`right`) + descendant `#text` paint ABOVE overlapping later normal-flow block background on both Draw IR (`cpu_simd`) and raster (`software`) lanes at `k=1` and `k=4`, while normal-flow `#text` paints ABOVE the float. |
| `REQ-WEB-002` | `test/01_unit/browser_engine/grid_auto_track_template_chrome159_spec.spl` | Both wrapped `<div><div style="display:flex">` and direct `<div style="display:flex">` items inside `grid-template-columns: auto 1fr` size the `auto` track to max-content (`40px`, `%` margin = `0` intrinsically). |
| `REQ-WEB-003` | `test/01_unit/browser_engine/inline_item_layoutunit_ceil_pen_chrome159_spec.spl` + `flex_row_button_tabs_chrome159_spec.spl` + new button/input device-width spec | `@tag:in-development` removed; `<code>a</code> — renderable` exact pixel columns match Chrome 159; `<input type=button|submit>` and flex/inline buttons match Chrome `k=1`/`k=4` widths; `200px` button at `k=4` respects measure cap. |
| `REQ-WEB-004` | `test/01_unit/browser_engine/fractional_layout_followups_chrome159_spec.spl` | `vertical-align:top|bottom` device baseline at `k=4`, `inline-block` `hangs_from_baseline` at `k=1`, `clear` vs `margin-top`, SVG edge AA & post-clamp residual. |
| `REQ-WEB-005` | `test/03_system/app/browser/browser_interactive_window_spec.spl` | Click hit-test resolves `<a href>` & `<button>` targets, wheel delta clamps `scroll_y` in `[0, max_scroll_y]`, Back/Forward/Reload update session history, and `gui_window.spl` contains zero engine-render imports (JIT guard). |
| `REQ-WEB-006` | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine2d_resolver_agreement_spec.spl` + `web_render_draw_ir_material_fallback_spec.spl` | Facade and renderer report identical resolved backend + honest fallback receipts. |
| `REQ-WEB-008` | `scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs`, `scripts/check/check-widget-shells-crossengine-evidence.shs` | `mismatch_count=0` (Node bitmap), `>= 80%` Chrome/Electron non-text parity (macOS). |

## 2. Generated Spec Docs Policy
- Executable `.spl` specs live strictly under `test/`.
- Generated/manual Markdown manuals live under `doc/06_spec/` (`find doc/06_spec -name '*_spec.spl' | wc -l` MUST equal `0`).
- Every test uses built-in matchers (`to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`) and real pixel/DOM assertions.
