# Simple Web Renderer Chrome Compatibility Corpus Plan

Feature: `simple_web_renderer_chrome_compat_corpus`

Scope:

- Add a deterministic offline corpus with more than 100 famous-site-inspired sample pages.
- Keep each sample self-contained HTML so it can be rendered by Chrome, Simple Web Renderer, and QEMU screenshot harnesses without network access.
- Gate corpus shape with BDD tests now; wire bulk Chrome baseline generation after the current 16-scene parity gate is stable.

Acceptance:

- `build_famous_site_sample_corpus()` returns at least 100 samples.
- Every sample has a stable id, display name, category, and complete HTML document.
- A Simple Web Renderer smoke test can render representative corpus pages to non-empty pixels.
- Future Chrome oracle work should use WPT reftest data, Playwright visual comparisons, or CDP `Page.captureScreenshot` rather than live scraping.

Out of scope:

- Claiming full Chrome compatibility.
- Fetching or storing live third-party site HTML.
- Bitwise acceptance for text-antialiased live pages.
