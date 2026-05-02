# Simple Browser Chromium HTML Parity Agent Tasks

Feature: `simple_browser_chromium_html_parity`

- Implement harness promotion in `src/app/wm_compare/html_compat.spl`.
- Keep renderer public entrypoints stable in `simple_web_renderer.spl` and `browser_renderer.spl`.
- Add fixed v1 widget fixtures and Chromium PPM baselines under `test/fixtures/html_compat/` and `test/baselines/html_compat/`.
- Add SPipe coverage for manifest/golden diagnostics and renderer non-empty buffers.
- Run focused parity checks plus renderer and wm_compare golden specs.
