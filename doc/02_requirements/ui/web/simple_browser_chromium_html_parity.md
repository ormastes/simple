# Simple Browser Chromium HTML Parity - Feature Requirements

Feature: `simple_browser_chromium_html_parity`

- REQ-001: The html-compat harness shall compare Simple-rendered ARGB buffers against checked-in Chromium PPM goldens by default.
- REQ-002: The harness shall regenerate Chromium `chrome.ppm` goldens only when `--update-baseline` is provided.
- REQ-003: The v1 manifest shall include text, block boxes, list, button, text input, card/panel, scrollable list, color, padding, and margin scenes at `320x240`.
- REQ-004: `BrowserRenderer.render_html_to_pixels`, `SimpleWebRenderer.render_html_to_pixels`, and `simple_web_render_html_to_pixels` shall return non-empty buffers of `width * height` pixels for the v1 scenes.
- REQ-005: Missing or mismatched Chromium goldens shall fail with a diagnostic that names the missing file or viewport mismatch.
- REQ-006: Each run shall write a report with viewport, capture source, tolerance, Simple result, Chromium result, and diff metrics.
