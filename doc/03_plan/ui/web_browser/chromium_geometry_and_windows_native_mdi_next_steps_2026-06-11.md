# Chromium Geometry And Windows Native MDI Next Steps

Date: 2026-06-11

Scope:

- Windows-native MDI/titlebar/button/input/event verification
- Deeper Chromium geometry extraction for Simple layout comparison

## Current Verified State

- Linux Electron MDI evidence is live and passing through
  `scripts/check/check-electron-mdi-evidence.shs`.
- macOS live-window wrapper exists, but this Linux host can only prove the
  explicit `requires-macos` skip lane.
- Windows-native MDI/titlebar evidence is still missing.
- Current checked-in Chromium parity lane is still the older
  `src/app/wm_compare/html_compat.spl` bitmap/golden subset plus
  `structural_layout_report.spl`.

## Windows Native Evidence Path

Reusable repo pieces:

- Win32 hosted backend:
  `src/os/compositor/hosted_backend_win32.spl`
- Win32 runtime bindings:
  `src/runtime/hosted/win32.rs`
  `src/runtime/hosted_win32.c`
- Windows launcher path:
  `bin/simple.cmd`
- Existing host WM automation:
  `src/lib/nogc_sync_mut/play/wm/mod.spl`
- Existing screenshot semantic validator shape:
  `scripts/check/ios_mdi_probe_server.spl`

Missing today:

- No Windows-only check wrapper that launches a real Win32-hosted MDI sample.
- No Windows-native screenshot verifier for titlebar/button/input/CSS/event
  proof.
- No Windows CI lane that runs GUI evidence instead of skipping it.

Smallest next implementation step:

1. Add a Windows-only evidence wrapper that launches a hosted Win32 MDI sample.
2. Use `std.play.wm` to enumerate/focus the window and capture a screenshot.
3. Reuse the current screenshot-proof style, but add Windows-native assertions:
   window found, title text visible, nonblank capture, expected MDI regions.

## Chromium Geometry Extraction Path

Useful existing repo pieces:

- Current parity harness:
  `src/app/wm_compare/html_compat.spl`
- Box/line report primitives:
  `src/app/wm_compare/structural_layout_report.spl`
- Existing Chrome metrics sidecars:
  `test/09_baselines/famous_site_corpus/*/chrome_metrics.json`
- Existing live browser screenshot producer:
  `tools/chrome-live-bitmap/capture_html_argb.js`
- Existing Electron selector audit / rect capture path:
  `tools/electron-live-bitmap/capture_html_argb.js`
- Existing in-repo Chromium devtools/session lane:
  `src/app/ui.chromium.devtools/*`

Recommended public Chromium surfaces:

- `DOMSnapshot.captureSnapshot(includeDOMRects=true, computedStyles=[...])`
- `Runtime.callFunctionOn` / `Runtime.evaluate` for
  `getBoundingClientRect()` and `getClientRects()`
- `DOM.getBoxModel` for CSS box debugging
- `Page.getLayoutMetrics` for coordinate normalization

Not recommended:

- Direct LayoutNG private-structure extraction as the primary integration path.
  It is too unstable compared with CDP.

Smallest next implementation step:

1. Add fixture-scoped geometry labels, for example `data-geom-label`.
2. Extend `tools/electron-live-bitmap/capture_html_argb.js` to emit
   `{label,x,y,width,height,text}` for labeled nodes.
3. Convert that output into `StructuralLayoutBox`.
4. Compare Chromium/Electron geometry against Simple-side exported boxes for
   one or two focused fixtures first.

2026-06-11 live evidence update:

- Steps 1-4 above now exist in a narrow real lane:
  - geometry export: `tools/electron-live-bitmap/capture_html_argb.js`
  - JSON-to-box bridge: `src/app/wm_compare/electron_geometry_compare.spl`
  - focused probe: `src/app/wm_compare/html_compat_geometry_probe.spl`
  - wrapper: `scripts/check/check-electron-html-compat-geometry-evidence.shs`
- Live `02_block_boxes` evidence now passes with `layout_match` and
  `mismatch_count=0`.
- The focused fix was two-part:
  - stop comparing Chromium against a guessed fixture model and instead read
    the Simple side from the renderer’s real Draw IR geometry export
  - add the missing default `body` margin (`8px`) in the Simple renderer so
    available-width block layout matches Chromium’s default document flow
- Live `03_list` evidence also passes with `layout_match` and
  `mismatch_count=0`.
- The focused list result did not require a renderer patch; it confirms the
  current Draw IR export and live Electron geometry lane already agree for this
  default block/list-item stacking case.
- Live `05_text_input` evidence now also passes with `layout_match` and
  `mismatch_count=0`.
- The focused input fix was:
  - add Chromium-like default input padding (`2px` horizontal, `1px` vertical)
  - treat explicit input `height` like content-box size plus padding/border,
    matching the already-correct explicit width behavior
- Live `04_button` evidence now also passes with `layout_match` and
  `mismatch_count=0`.
- The focused button fix was:
  - preserve the already-correct button box geometry
  - add the missing default bottom line-box contribution for buttons so the
    parent panel height matches Chromium
- Live `06_card_panel` evidence now also passes with `layout_match` and
  `mismatch_count=0`.
- The focused card-panel fix was:
  - restore a Chromium-like default paragraph bottom margin so parent block
    height accumulation matches
  - attach descendant text to labeled container boxes in the focused probe so
    structured geometry evidence carries the same text signal Chromium reports
- Live `07_scrollable_list` evidence now also passes with `layout_match` and
  `mismatch_count=0`.
- The focused scrollable-list fix was:
  - parse `overflow:auto` / `overflow-y:auto` as a vertical-scrollbar-reserving
    state in the renderer
  - reserve a Chromium-like scrollbar gutter for explicit-height block
    containers before sizing child block width, so the live overflow list width
    matches Chromium
- Live `13_margin` evidence now also passes with `layout_match` and
  `mismatch_count=0`.
- The focused margin fix was:
  - collapse adjacent vertical margins between stacked block siblings instead
    of summing both bottom and top margins
  - apply the same sibling-margin collapse in `display: contents` flow so the
    browser-computed stacked y positions and parent height match Chromium
- Live `14_border` evidence now also passes with `layout_match` and
  `mismatch_count=0`.
- The focused border result rides on the same corrected sibling vertical
  margin-collapse behavior and confirms border edges now propagate with the
  browser-matched stacked geometry in this fixture.
- Live `16_flex_row` evidence now also passes with `layout_match` and
  `mismatch_count=0`.
- The focused flex-row fix was:
  - add a dedicated `display:flex; flex-direction:column` layout path instead
    of falling back to block-flow margin-collapse semantics
  - preserve non-collapsing flex-item margins in the vertical parent while
    keeping the existing row-container width distribution for the nested
    `#middle` flex row
- Live `17_flex_col` evidence also passes with `layout_match` and
  `mismatch_count=0`.
- The focused flex-column result confirms the same new flex-column path also
  matches Chromium when both the outer container and nested `#middle` container
  use `flex-direction: column`.
- Interpretation:
  - the focused block-wrapper parity gap for `02_block_boxes` is closed in the
    live Chromium/Electron geometry lane
  - the focused default list/block stacking case for `03_list` is also closed
    in the same live lane
  - the focused button control geometry gap for `04_button` is also closed in
    the same live lane
  - the focused text-input control geometry gap for `05_text_input` is also
    closed in the same live lane
  - the focused card/container text geometry gap for `06_card_panel` is also
    closed in the same live lane
  - the focused overflow/scrollbar width gap for `07_scrollable_list` is also
    closed in the same live lane
  - the focused sibling vertical margin-collapse gap for `13_margin` is also
    closed in the same live lane
  - the focused bordered stacked block geometry for `14_border` is also closed
    in the same live lane
  - the focused flex-column parent plus nested flex-row geometry for
    `16_flex_row` is also closed in the same live lane
  - the focused flex-column parent plus nested flex-column geometry for
    `17_flex_col` is also closed in the same live lane
  - broader geometry parity is still incomplete; this is one verified case, not
    completion of the full layout objective

## This Turn's Code Increment

The in-repo Chromium devtools mirror/session now has a geometry storage hook:

- `src/app/ui.chromium.devtools/dom_mirror.spl`
- `src/app/ui.chromium.devtools/attach_session.spl`

This is only storage, not live CDP extraction yet. It gives the Chromium lane
an in-tree destination for per-node bounds before wiring a browser-side
extractor.
