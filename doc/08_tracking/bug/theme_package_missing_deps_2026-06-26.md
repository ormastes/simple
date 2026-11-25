# Bug: theme_package_spec — missing runtime dependencies
## RESOLVED 2026-11-25 — spec green 19/19; see "Resolution 2026-11-25" section at end of file

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Still OPEN 2026-09-13 — premise unchanged: `src/app/ui/web/` is still empty
- **measured**: `ls src/app/ui/web/` returns nothing — `html.spl` and `generate_css` were never implemented, so the spec's first import still cannot resolve.
- **measured**: `test/01_unit/lib/common/ui/theme_package_spec.spl` still exists, so the blocked coverage is still on the books.
- **inferred**: not closed as stale — this is a real unimplemented module, not a dead reference. Implementing it is out of scope for a triage pass.

**Date:** 2026-06-26
**Spec:** `test/01_unit/lib/common/ui/theme_package_spec.spl`
**Status:** RESOLVED 2026-11-25 (historical report below kept verbatim; see the Resolution 2026-11-25 section)

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


## Resolution 2026-11-25 — spec green (19/19); two of three original gaps were already fixed elsewhere

Verified and fixed on Windows worktree `D:\wt-p3-bae` (branch
`work/p3-bae-20261125`, base `origin/release/1.0.0`), tracked `bin/simple.exe`,
`SIMPLE_LIB=src`, `--mode=interpreter`.

### State found (2026-11-25)

- `src/app/ui.web/html.spl` now exists with `pub fn generate_css(theme: text) -> text`
  (line 277) — original failure 1 fixed by other work. The premise line
  "`src/app/ui/web/` is still empty" was stale: the directory is now the
  `ui.web` dotted-module directory and is populated.
- `src/os/compositor/browser_backend.spl` now defines `theme_bg` (line 46) and
  `theme_accent` (line 52) — original failure 3 fixed by other work.
- `simple_web_app_html_with_theme` still existed nowhere (original failure 2).
- New since the last triage: the spec's duplicate import
  `use common.ui.theme_package.{...}` was dangling — the module was moved to
  `nogc_sync_mut/ui/theme_package.spl` by the deliberate layering refactor
  `3d2141deaa0` (2026-06-02, "fix common/ui layering violations"). The spec
  failed module resolution there before any assertion ran:
  `error: semantic: Cannot resolve module: common.ui.theme_package`.

### Changes made

1. `test/01_unit/lib/common/ui/theme_package_spec.spl` — removed the dangling
   duplicate `use common.ui.theme_package.{...}` block; the identical 9-name
   import from `nogc_sync_mut.ui.theme_package` (the module's real home since
   `3d2141deaa0`) is retained. No assertion touched.
2. `src/os/compositor/simple_web_window_renderer.spl` — implemented the
   missing `pub fn simple_web_app_html_with_theme(theme, title, body_html)` as
   the app-window variant of `simple_web_content_full_html_with_theme`:
   `.wm-app-container` > `.wm-app-titlebar` (title) + `.wm-app-content`
   (body), themed CSS from `_simple_web_window_css(theme)` (package CSS +
   structural CSS), material fallback attrs, and a
   `data-wm-shell='SimpleOS shell via Simple Web'` provenance attribute. This
   is the "add the function" option the bug's Fix Required section names.
3. `src/app/ui.web/_HostTaskbarRuntime/mode_and_layout_helpers.spl` —
   repointed the dangling `use common.ui.theme_package.{default_theme_id}` to
   `nogc_sync_mut.ui.theme_package` (the name is actually called at line 85;
   this was a live unresolved-import landmine). Same refactor-missed caller
   class as the 90+ updated in `3d2141deaa0`.
4. `src/os/compositor/simple_gui_window_renderer.spl` — removed its unused
   dangling `use common.ui.theme_package.{default_theme_id}` (imported, never
   called).

### Evidence

- BEFORE (stash of the four edits, same binary):
  `theme_package_spec.spl` outcome=ERROR, `Cannot resolve module:
  common.ui.theme_package`, 0 of >=19 declared tests executed.
- AFTER: `theme_package_spec.spl` outcome=OK, `declared>=19 executed=19
  passed=19 failed=0`, `PASS`, exit 0.
- Neighbor consumer `test/01_unit/os/apps/file_explorer/finder_spec.spl`
  (also imports `simple_web_app_html_with_theme`): BEFORE 44/56 passed,
  AFTER 47/56 passed — strictly better, no regressions. Its remaining 9
  failures are a different, larger feature (Finder-app HTML dispatch:
  `finder-sidebar`/`finder-columns`/`finder-preview` rendering from state
  text, plus 2 `default_manifests` Finder-entry assertions) that predates this
  change and is not part of this bug's scope.

The 2026-09-16 "Open — needs owner triage" header is superseded: the spec this
bug tracks is fully green.
