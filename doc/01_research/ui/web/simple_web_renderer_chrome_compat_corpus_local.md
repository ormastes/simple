# Simple Web Renderer Chrome Compatibility Corpus - Domain Research

Feature: `simple_web_renderer_chrome_compat_corpus`

Chrome-perfect compatibility is not a single switch. The practical browser-engine path is a deterministic corpus with Chrome as oracle, then broader standards coverage through Web Platform Tests.

Findings:

- Web Platform Tests has a visual/reftest model for browser rendering comparisons, including screenshot timing around reftest completion: https://web-platform-tests.org/writing-tests/visual.html
- Playwright Test has native screenshot comparison through `toHaveScreenshot()`, with repeated capture until stable output before snapshot comparison: https://playwright.dev/docs/next/test-snapshots
- Current Playwright documentation recommends `toHaveScreenshot()` for page and element screenshots, notes that browser rendering varies by OS, hardware, settings, headless mode, and related factors, and exposes strict gates such as `maxDiffPixels`: https://playwright.dev/docs/test-snapshots
- Playwright's visual comparison path uses `pixelmatch`; pixelmatch itself is a raw image-data comparator with perceptual color difference and anti-aliased-pixel handling, and its CLI/API return the mismatched pixel count: https://github.com/mapbox/pixelmatch
- Chrome DevTools Protocol exposes `Page.captureScreenshot`, which is the correct low-level Chrome oracle API when the project outgrows Electron wrapper capture: https://chromedevtools.github.io/devtools-protocol/tot/Page/#method-captureScreenshot

Decision:

- Keep live famous-site pages out of the bitwise gate because content, ads, A/B tests, fonts, geo routing, time, and login state make bitwise evidence unstable.
- Add an offline 100+ famous-site-inspired sample corpus that exercises common page shapes without copying site markup.
- Use Playwright/Chromium screenshots as the Chrome oracle, convert to PPM for
  Simple-native comparison, and keep the project's `analyze_ppm_delta.js`
  because it gives repo-specific SDN/PPM diagnostics, DOM-metrics regions, and
  exact bitwise counts without adding a PNG dependency to the Simple runner.
- Keep `pixelmatch` as the reference external comparator model for future PNG
  or Playwright-native lanes, but do not replace the current PPM analyzer until
  the corpus can preserve the same exact-count, SAD, color-class, and per-line
  diagnostics.
- Plan a future WPT/imported-reftest lane for standards breadth.
