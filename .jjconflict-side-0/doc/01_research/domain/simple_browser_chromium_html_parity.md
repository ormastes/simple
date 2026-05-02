# Simple Browser Chromium HTML Parity - Domain Research

Feature: `simple_browser_chromium_html_parity`

Chromium/Electron remains the visual oracle for this gate. The feature does not attempt Acid-style browser compatibility; it locks a small widget-scene subset against deterministic Chromium screenshots at `320x240`.

Reference policy:

- Chromium output is captured through the existing Electron screenshot tool.
- Normal gate runs load checked-in `chrome.ppm` files.
- Regeneration is explicit through `--update-baseline`.
- Simple browser rendering remains in-process through `simple_web_render_html_to_pixels` and the render-scene software executor.

The comparison model follows the existing wm_compare drift policy: exact comparison first, then perceptual comparison with a `9900/10000` match floor, equivalent to a maximum `1%` perceptual diff budget.
