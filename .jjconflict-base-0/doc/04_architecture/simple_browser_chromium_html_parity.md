# Simple Browser Chromium HTML Parity Architecture

Feature: `simple_browser_chromium_html_parity`

This extends the drawing-stack architecture with an HTML widget golden gate.

Flow:

1. `html_compat.build_catalog()` defines the fixed v1 scene manifest.
2. `load_combined_html()` resolves HTML plus optional CSS.
3. Default mode loads `test/baselines/html_compat/<scene>/chrome.ppm`.
4. Simple mode renders through `simple_web_render_html_to_pixels`.
5. `compare_pair()` runs exact diff first and perceptual diff second.
6. `write_report()` records viewport, tolerance, capture source, results, and metrics.

Electron/Chromium is not a runtime backend for Simple browser rendering in this feature. It is only the oracle used to regenerate checked-in `chrome.ppm` references.

The hot path is intentionally software-only: DOM/CSS/layout/scene generation and `execute_scene_to_buffer`. Engine2D backend startup is outside this gate because it introduces backend init cost and interpreter-specific failures unrelated to HTML visual parity.
