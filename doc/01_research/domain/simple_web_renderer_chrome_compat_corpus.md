# Simple Web Renderer Chrome Compatibility Corpus - Domain Research

Feature: `simple_web_renderer_chrome_compat_corpus`

Chrome-perfect compatibility is not a single switch. The practical browser-engine path is a deterministic corpus with Chrome as oracle, then broader standards coverage through Web Platform Tests.

Findings:

- Web Platform Tests has a visual/reftest model for browser rendering comparisons, including screenshot timing around reftest completion: https://web-platform-tests.org/writing-tests/visual.html
- Playwright Test has native screenshot comparison through `toHaveScreenshot()`, with repeated capture until stable output before snapshot comparison: https://playwright.dev/docs/next/test-snapshots
- Chrome DevTools Protocol exposes `Page.captureScreenshot`, which is the correct low-level Chrome oracle API when the project outgrows Electron wrapper capture: https://chromedevtools.github.io/devtools-protocol/tot/Page/#method-captureScreenshot

Decision:

- Keep live famous-site pages out of the bitwise gate because content, ads, A/B tests, fonts, geo routing, time, and login state make bitwise evidence unstable.
- Add an offline 100+ famous-site-inspired sample corpus that exercises common page shapes without copying site markup.
- Use the existing Chromium PPM path for small golden scenes, and plan a future WPT/imported-reftest lane for standards breadth.
