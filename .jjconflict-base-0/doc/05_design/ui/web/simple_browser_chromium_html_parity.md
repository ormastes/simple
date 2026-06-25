# Simple Browser Chromium HTML Parity Detail Design

Feature: `simple_browser_chromium_html_parity`

Implementation points:

- `html_compat.spl` exposes the small manifest API: catalog, HTML resolution, Chromium golden loading, Simple pixel capture, comparison, and regeneration.
- `--update-baseline --skip-simple` sweeps Chromium reference generation without requiring Simple rendering.
- Normal mode never overwrites `chrome.ppm`; it writes `simple.ppm`, diff PPMs on mismatch, and `report.sdn`.
- `BrowserRenderer.render_html_to_pixels` wraps the stable software pixel-array renderer while preserving the public result object.
- Browser text layout/paint measurement uses deterministic monospace metrics to avoid interpreter-only `FontRenderer` mutation failures.

Error handling:

- Missing `chrome.ppm`: `CaptureResult.success=false` with the path in `error`.
- Viewport mismatch: `CaptureResult.success=false` with actual and expected dimensions.
- Empty or wrong-sized Simple buffer: `CaptureResult.success=false` with observed and expected sizes.
