# Bug: theme_package_spec — missing runtime dependencies

**Date:** 2026-06-26
**Spec:** `test/01_unit/lib/common/ui/theme_package_spec.spl`
**Status:** Cannot fix — multiple modules have no git history

## Failures

The spec imports three modules that do not exist on disk or in git history:

1. **`use app.ui.web.html.{generate_css}`** — `src/app/ui/web/` directory is empty and `html.spl` has zero git history. The function `generate_css` was never committed.

2. **`use os.compositor.simple_web_window_renderer.{simple_web_app_html_with_theme}`** — `src/os/compositor/simple_web_window_renderer.spl` exports `themed_simple_web_html_with_theme` and `simple_web_themed_render_request_with_theme` but NOT `simple_web_app_html_with_theme`. Name mismatch; no matching git history.

3. **`use os.compositor.browser_backend.{theme_bg, theme_accent}`** — `browser_backend.spl` was restored from git but the compiler reports `BrowserBackend does not implement required method name from trait RenderBackend` (puzzling since the trait only has `fn backend_name()` not `fn name()`). Functions `theme_bg` and `theme_accent` may also be missing.

## Root Cause

`app.ui.web.html` was never committed to the repository. The spec was written ahead of its implementation. The other two symbols are name mismatches or regressions from a refactor that renamed exported functions.

## Impact

`test/01_unit/lib/common/ui/theme_package_spec.spl` — 0/1 load (module resolution fails before any assertions run).

## Fix Required

- Implement `src/app/ui/web/html.spl` with `generate_css(theme: text) -> text`
- Add `fn simple_web_app_html_with_theme` to `simple_web_window_renderer.spl` (or update spec to use `themed_simple_web_html_with_theme`)
- Investigate `BrowserBackend` trait impl error and add `theme_bg`/`theme_accent` exports
