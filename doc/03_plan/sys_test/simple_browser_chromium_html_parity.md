# Simple Browser Chromium HTML Parity System Test Plan

Feature: `simple_browser_chromium_html_parity`

SSpec coverage:

- `test/sys/wm_compare/html_compat_spec.spl` checks manifest contents, fixture resolution, Chromium golden loading, and viewport mismatch diagnostics.
- `test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` checks `BrowserRenderer.render_html_to_pixels` and `SimpleWebRenderer` return non-empty buffers.

Manual/focused parity checks:

- `bin/simple run src/app/wm_compare/html_compat.spl --only=00_text_only`
- `bin/simple run src/app/wm_compare/html_compat.spl --only=04_button`
- `bin/simple run src/app/wm_compare/html_compat.spl --only=05_text_input`
- `bin/simple run src/app/wm_compare/html_compat.spl --only=06_card_panel`
- `bin/simple run src/app/wm_compare/html_compat.spl --only=07_scrollable_list`

Regression checks:

- `bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
- `bin/simple test test/sys/wm_compare/html_compat_spec.spl`
- `bin/simple test test/sys/wm_compare/golden_gate_spec.spl`
