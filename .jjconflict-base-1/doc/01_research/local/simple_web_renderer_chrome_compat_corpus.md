# Simple Web Renderer Chrome Compatibility Corpus - Local Research

Feature: `simple_web_renderer_chrome_compat_corpus`

Date: 2026-05-05

Local components inspected:

- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl`
  wraps `BrowserRenderer` as the public Simple Web Renderer API and exposes
  HTML/URL-to-scene and HTML/URL-to-pixels helpers.
- `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`
  owns the DOM/style/layout/paint-to-scene/pixel path and the Engine2D-backed
  renderer constructor variants.
- `src/app/wm_compare/html_compat.spl`
  is the Chromium-vs-Simple PPM screenshot harness. It loads checked-in Chrome
  baselines, captures Simple output through a child worker, compares exact
  pixels, and writes SDN reports.
- `src/app/wm_compare/simple_html_capture_worker.spl`
  is the bounded child process used as source B for Simple Web Renderer
  screenshots.
- `src/app/wm_compare/site_corpus.spl`
  builds deterministic famous-site-inspired sample pages for corpus smoke
  coverage.
- `test/sys/wm_compare/html_compat_spec.spl`
  covers the 16-scene manifest, golden loading, timeout parsing, and bitwise
  compare core.
- `test/sys/wm_compare/famous_site_corpus_spec.spl`
  verifies the corpus has more than 100 complete deterministic pages and that
  representative samples render to non-empty pixels.
- `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`
  covers BrowserRenderer pixel output, Engine2D backend consistency, and sampled
  CSS fixture paths.
- `test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
  covers the public Simple Web Renderer API and its default software backend.

Call chain summary:

`SimpleWebRenderer.render_html_to_pixels` delegates to
`BrowserRenderer.render_html_to_pixels`. The compatibility harness writes a
combined HTML fixture to `/tmp`, launches `simple_html_capture_worker.spl`, then
decodes the worker PPM and compares it to
`test/baselines/html_compat/<id>/chrome.ppm`.

Current local findings:

- The renderer has a working Engine2D/software pixel path and direct tests for
  the bridge.
- The 16-scene HTML compatibility gate is executable and has exact/perceptual
  reporting.
- The 100+ corpus is deterministic and offline, but only smoke-rendered today.
- Several compatibility scenes are fixture-specific rectangle paths rather than
  a general Chrome-compatible DOM/CSS/text implementation.
- Hard Chrome antialiasing cases still use marker/baseline scaffolding in the
  screenshot gate.

Local blockers:

- General text shaping/rasterization is incomplete.
- General CSS cascade/layout is incomplete; many current paths are
  fixture-bounded.
- Border antialiasing is approximate in `BrowserRenderer` and scaffolded in the
  screenshot harness.
- The 100+ corpus does not yet have Chrome oracle screenshots or bitwise
  reports.
