# BUG: Tauri mobile webview paints blank white on both iOS sim and Android emulator despite `eval OK` / render pipeline "succeeding"

**Status:** FIXED. Patch applied and committed (see Fix section for sha). Priority: P0 (both
mobile lanes render nothing visible) — root render-pipeline bug resolved; iOS-simulator
end-to-end re-verification remains a follow-up item (see Verification below).

## Symptom

Per `doc/09_report/mobile_p0_lane_reverification_2026-07-08.md` (2026-07-07 session): both the
iOS 17 simulator and the Android Pixel7 emulator build, install, and launch the Tauri shell
cleanly. Logs on both platforms show the full pipeline firing:

```
[tauri-shell] render, html_len=336705
[tauri-shell] eval OK
```

...but the on-screen capture (simctl screenshot / adb screencap) is **blank white** — no dark
theme, no widgets — on both platforms, with the identical `html_len=336705` byte count. The
guide's own June 2026-06-06 evidence entry (`tauri_mobile_guide.md:84`) records a *successful*
render at `html_len≈346 KB` for the same 33+13-widget showcase — a materially different byte
count from the 336,705 bytes seen now.

## Root cause

`src/lib/common/ui/parse/sdn_tree.spl` (the **pure**, file-I/O-free SDN→UITree builder used by
`common.ui.*`) defines and exports a second, broken `parse_ui_to_tree`:

```simple
fn parse_ui_to_tree(path: text) -> Result<UITree, text>:
    build_tree_from_source("")

export parse_ui_to_tree
```

This ignores its `path` argument entirely and always parses an **empty string**. It is a
same-named duplicate of the correct, file-reading `parse_ui_to_tree` in
`src/lib/nogc_sync_mut/ui/parse/sdn_tree.spl` (which does `read_file(path)` then delegates to
`build_tree_from_source(source)`), and it is the only other place in the tree defining a
function with this exact name.

The real render path (`src/app/ui.tauri/app.spl` → `TauriApp.new_from_backend` →
`parse_ui_to_tree(file_path)`, imported via `use nogc_sync_mut.ui.parse.sdn_tree.{parse_ui_to_tree}`)
is architecturally correct. But `src/lib/gc_async_mut/gpu/browser_engine/glass_pipeline_compare.spl`
imports the *other*, broken one instead (`use common.ui.parse.sdn_tree.{parse_ui_to_tree}`), and
also expects it to read `sdn_path` from disk — so that call site is independently broken too.
When both modules are present in the same program's module graph, the two same-named top-level
functions collide (this codebase's known cross-module symbol-resolution class of bug — see
project memory `ref_architecture.md` / prior "global import map" fixes) and the empty-string
stub wins, so `TauriApp` ends up with a UITree parsed from `""`.

Parsing `""` through `build_tree_from_source_unchecked` produces: `app.title`/`app.theme` both
empty (theme falls back, title falls back), and `build_widget_node(entries, "layout", 0)` with
no `.type` entry at path `"layout"` → `kind` defaults to `"panel"`, `id` defaults to
`"layout"`, and **zero children** (no entries at all to recurse into). This renders as:

```html
<div class="widget-panel layout-vbox focused" id="layout" style="flex: 1;">
  <div class="panel-content"></div>
</div>
```

— a single empty panel div, ~140 bytes of body content buried inside ~336 KB of (correctly
generated, unrelated) global CSS. The CSS *is* present and applied (no media-query gating bug,
no viewport bug, no webview-config bug) — there is simply no widget markup to style, hence
"blank white": a fully-styled page with an empty body.

## Evidence

Reproduced directly (not just inferred from logs) by regenerating the exact same render path
the shell uses (`examples/06_io/ui/render_mobile_page.spl` against
`examples/06_io/ui/widget_showcase_mobile.ui.sdn`, same `generate_css` + `render_html_tree` +
`web_render_to_artifact` calls the shell's `tauri_render_ipc_json` uses):

- **Before fix** (current `main`): wrote 336,671 bytes; body content is exactly the 140-byte
  empty `id="layout"` panel described above. This is a byte-for-byte match in scale to the
  336,705 bytes logged by both mobile lanes in the P0 report.
- **After fix** (broken duplicate `parse_ui_to_tree` removed from
  `common/ui/parse/sdn_tree.spl`, and `glass_pipeline_compare.spl`'s import repointed at the
  correct `nogc_sync_mut.ui.parse.sdn_tree.{parse_ui_to_tree}`): wrote 346,701 bytes; body
  contains the real tree — `id="root"`, `<nav class="widget-navigation-bar">`, heading, intro
  text, tabs, command palette, confirm dialog, bottom sheet, etc. **346,701 bytes matches the
  guide's recorded 2026-06-06 "Verified live" evidence of `html_len≈346 KB` almost exactly** —
  strong corroboration that this duplicate-symbol collision is the exact regression that broke
  rendering between the June evidence and the current P0 lane failure, not a webview/shell/CSS
  issue.
- Rendered the fixed HTML in headless Chrome at a 390×844 (iPhone) viewport
  (`chrome --headless=new --screenshot`) and confirmed visually: full dark glass showcase with
  navigation bar, tabs, properties panel, command palette, confirm dialog, and bottom sheet all
  visible and styled — not blank.
- Desktop-first control test (per task instructions) therefore also answers step 1 of the
  investigation: the *generated page itself* was broken (336 KB of CSS, ~140 bytes of body), not
  the mobile shell/webview config — confirmed independent of any mobile simulator/emulator.

## Fix (applied and committed)

Two files, both required together:

1. `src/lib/common/ui/parse/sdn_tree.spl` — delete the broken duplicate:
   ```simple
   fn parse_ui_to_tree(path: text) -> Result<UITree, text>:
       build_tree_from_source("")

   export parse_ui_to_tree
   ```
   This module is documented as "self-contained ... works independently of file access" (see
   its own header comment) — a `path`-taking, file-reading-shaped function never belonged here.
2. `src/lib/gc_async_mut/gpu/browser_engine/glass_pipeline_compare.spl` line 11 — repoint the
   import from the (now-removed) broken stub to the real file-reading implementation:
   ```diff
   -use common.ui.parse.sdn_tree.{parse_ui_to_tree}
   +use nogc_sync_mut.ui.parse.sdn_tree.{parse_ui_to_tree}
   ```
   Without this, `glass_pipeline_compare.spl`'s own three call sites
   (`render_both_pipelines`, `render_web_pipeline_only`, `render_engine_pipeline_only`) would
   fail to resolve `parse_ui_to_tree` at all — they already expect it to read `sdn_path` from
   disk (same latent bug, just uncalled by the P0 lanes).

Verified: after applying both changes, regenerating the same showcase page produces the correct
346,701-byte page with full widget markup (see Evidence). Applied at commit `<FIX_SHA>` (see
`jj log`/`git log` for `doc/08_tracking/bug/tauri_mobile_webview_blank_white_render_2026-07-08.md`).

## Verification (integration pass, 2026-07-07)

- **Sanity grep:** searched the whole repo for every remaining importer of `parse_ui_to_tree`.
  All active app/lib/example/numbered-test call sites (`src/app/ui.*`, `src/app/ui.mcp`,
  `test/01_unit/**`, `test/02_integration/**`, `test/03_system/**`, `examples/06_io/ui/**`)
  already imported `nogc_sync_mut.ui.parse.sdn_tree.{parse_ui_to_tree}` — the correct
  implementation — and are unaffected by the deletion. The only importers of the *deleted*
  `common.ui.parse.sdn_tree.{parse_ui_to_tree}` besides `glass_pipeline_compare.spl` are stale,
  pre-existing duplicate test trees (`test/system/gui/*`, `test/unit/app/ui/backend_matrix_spec.spl`
  — unnumbered leftovers from the `test/` → `test/0N_*` migration). Confirmed these were already
  RED before this fix (e.g. `test/system/gui/sdn_parsing_spec.spl` was 9 passed / 9 failed
  pre-patch; `test/unit/app/ui/backend_matrix_spec.spl` fails to resolve unrelated modules
  — `app.ui.render.widgets`, `app.ui.web.backend` — that don't exist in the current tree at all).
  No regression; out of scope for this fix (separate stale-test-tree cleanup).
- **Regeneration:** `SIMPLE_EXECUTION_MODE=interpret bin/simple run examples/06_io/ui/render_mobile_page.spl
  -- examples/06_io/ui/widget_showcase_mobile.ui.sdn <out>.html` wrote exactly **346,701 bytes**
  (matches the Evidence section above), containing `id="root"`, `widget-navigation-bar`,
  `widget-tabs`/`tab-bar-item`, `widget-dialog`, etc. — the full tree, not the 140-byte empty
  panel.
  Also regenerated `tools/tauri-shell/dist/index.html` from the same command (build artifact,
  untracked by VCS — reverted to its stale committed 14,626-byte placeholder afterward so the
  working tree stays clean; see prior precedent in this same doc history).
- **Headless Chrome screenshot** at 390×844 (`Google Chrome --headless --window-size=390,844
  --screenshot`) of the regenerated HTML: 100% non-white pixels; visually confirmed dark-theme
  "Widget Showcase" page with nav/tab bar (Home/Search/Profile), Properties panel, command
  palette, "Confirm Action" dialog, and "More Options" bottom sheet — definitively not blank.
- **Specs:**
  - `test/01_unit/app/ui/browser_backend_pixel_paths_spec.spl` — 4/4 PASS.
  - `test/03_system/gui/glass_pixel_compare_spec.spl` — 8/13 pass, same 4 pre-existing failures
    as before the fix (`ComparisonResult` missing `total_pixels` field / `len` method — an
    unrelated, pre-existing bug in `glass_pipeline_compare.spl`'s comparison result type) plus
    one *additional* failure ("runs core glass comparison") that was previously a false-pass:
    with the broken empty-string stub, this example never reached the code path that touches
    `ComparisonResult.total_pixels`, so it looked green; with real parsing restored it now hits
    the same genuine pre-existing bug the other 4 failures hit. Net: no new distinct root cause,
    one fewer false-positive. Filed as a follow-up (`ComparisonResult.total_pixels`/`len` gap)
    rather than fixed here (out of scope).
  - `test/02_integration/rendering/glass_pipeline_screenshot_spec.spl` — fails to resolve module
    `common.ui.glass_test_page`; confirmed pre-existing/unrelated (same failure with the patch
    reverted).
- **`bin/simple check`** on both touched files: `All checks passed (1 file(s))` for both.
- **`sh scripts/check/check-ui-backend-isolation.shs`**: `ui_backend_isolation_new=0`,
  `ui_backend_isolation_ok=true` (baseline drift of 1 pre-existing, unrelated to this change and
  already dirty in the working copy before this task started).
- **iOS simulator (bonus, time-boxed) — SKIPPED, remaining P0 verification item:** built and
  installed the Tauri iOS app (`cargo tauri ios build --debug --target aarch64-sim`, launched on
  a booted iPhone 17 Pro sim). Discovered the mobile shell does **not** load
  `tools/tauri-shell/dist/index.html` as a static asset on mobile — `src-tauri/src/lib.rs`
  spawns an embedded/bundled `simple` runtime binary (baked in via `include_bytes!` at Rust
  build time) as a subprocess over IPC, fronted by an inline `mdi_shell_html()` shell page, and
  only falls back to `WebviewUrl::App("index.html")` in non-MDI/non-shared-wm modes. The
  embedded runtime binary was not rebuilt from this source fix, so an iOS-sim screenshot
  wouldn't actually exercise the fixed code path without also rebuilding/re-embedding that
  runtime — out of scope for this fix's time budget. Desktop-lane verification (regeneration +
  headless Chrome screenshot above) already proves the fix at the render-pipeline level; the
  mobile IPC/bundled-runtime rebuild-and-relaunch is the remaining P0 acceptance step for a
  future pass.

## Secondary finding (already fixed in this pass, low-risk)

The guide's `## 2. Responsive layout` section still said breakpoints are `601–1200px`
(tablet) / `>1200px` (desktop). The code-authoritative `default_breakpoints()` (600/840, per
`test/01_unit/lib/common/ui/responsive_css_parity_spec.spl`, 6/6 passing) changed in the
2026-06-13 adaptive-scaffold work; the guide prose was never updated. Fixed in
`doc/07_guide/platform/mobile/tauri_mobile_guide.md` in this pass (see commit). This is
unrelated to the blank-render bug — the breakpoints just restyle at different widths, they
never hide content — but was called out as a known-stale doc in the P0 report and in scope for
this task.

## Files

- `src/lib/common/ui/parse/sdn_tree.spl` (bug: broken duplicate `parse_ui_to_tree`)
- `src/lib/gc_async_mut/gpu/browser_engine/glass_pipeline_compare.spl` (bug: imports the broken
  duplicate, and independently expects file-reading behavior from it)
- `src/lib/nogc_sync_mut/ui/parse/sdn_tree.spl` (the correct implementation, unaffected)
- `src/app/ui.tauri/app.spl`, `src/app/ui.tauri/backend.spl` (render call path, confirmed
  correct — imports the right module)
- Evidence: `doc/09_report/mobile_blank_render_debug_2026-07-08.md` (uncommitted)
- Patch: `/private/tmp/claude-501/-Users-ormastes-simple/7597a415-f0b0-4c3f-822d-107292b34bec/scratchpad/mobile_blank_fix.patch`
