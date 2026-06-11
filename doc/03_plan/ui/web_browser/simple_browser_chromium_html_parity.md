# Simple Browser Chromium HTML Parity System Test Plan

Feature: `simple_browser_chromium_html_parity`

Current state as of 2026-06-11:

- The authoritative current harness in this worktree is still the older
  `src/app/wm_compare/html_compat.spl` catalog covering fixtures
  `00..07` and CSS layers `10..17`.
- The newer focused fixture lane described in some earlier progress notes
  (`146+`, client-rect/box-model parity rows, no-cheat guard summaries) is not
  present in the current worktree and must not be treated as current evidence.
- Current checked-in parity scope is still a mixed bitmap/golden lane. It is
  useful for regression pressure, but it is not yet broad Chromium layout-engine
  parity.
- Text input/titlebar-related fixtures that do exist in the current lane are
  `04_button`, `05_text_input`, `06_card_panel`, and `07_scrollable_list`.

SPipe coverage:

- `test/03_system/wm_compare/html_compat_spec.spl` checks manifest contents, fixture resolution, Chromium golden loading, and viewport mismatch diagnostics.
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` checks `BrowserRenderer.render_html_to_pixels` and `SimpleWebRenderer` return non-empty buffers.

Manual/focused parity checks:

- `bin/simple run src/app/wm_compare/html_compat.spl --only=00_text_only`
- `bin/simple run src/app/wm_compare/html_compat.spl --only=01_inline_text`
- `bin/simple run src/app/wm_compare/html_compat.spl --only=04_button`
- `bin/simple run src/app/wm_compare/html_compat.spl --only=05_text_input`
- `bin/simple run src/app/wm_compare/html_compat.spl --only=06_card_panel`
- `bin/simple run src/app/wm_compare/html_compat.spl --only=07_scrollable_list`

Regression checks:

- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
- `bin/simple test test/03_system/wm_compare/html_compat_spec.spl`
- `bin/simple test test/03_system/wm_compare/golden_gate_spec.spl`

Open gaps tied to the active browser objective:

- No current checked-in focused fixture lane for deeper flex/grid/LayoutNG-style
  geometry comparison.
- No current direct Chromium layout extraction/access path in this worktree.
- Existing `05_text_input` bitmap baseline is still non-accepted evidence in
  `test/09_baselines/html_compat/05_text_input/report.sdn`, so input visual
  parity remains incomplete.
- A new narrow live geometry lane now exists for `02_block_boxes` and is
  currently passing:
  - wrapper: `scripts/check/check-electron-html-compat-geometry-evidence.shs`
  - probe: `src/app/wm_compare/html_compat_geometry_probe.spl`
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: use renderer-backed Draw IR geometry on the Simple side and
    apply Chromium-compatible default `body` margins in the renderer
- The same live geometry lane now passes for `03_list`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: confirms current default block/list-item stacking already
    matches live Chromium/Electron geometry for this fixture without a renderer
    patch
- The same live geometry lane now passes for `05_text_input`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: Chromium-like default input padding plus explicit input height
    as content-box size plus padding/border
- The same live geometry lane now passes for `04_button`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: preserve button box size and add the missing default button
    line-box/baseline contribution so the parent panel height matches Chromium
- The same live geometry lane now passes for `06_card_panel`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: restore Chromium-like paragraph default bottom margin for
    parent height accumulation and attach descendant text to labeled container
    boxes in the focused probe
- The same live geometry lane now passes for `07_scrollable_list`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: parse `overflow:auto` as a vertical-scrollbar-reserving state
    and reserve a Chromium-like scrollbar gutter for explicit-height block
    containers before sizing child block width
- The same live geometry lane now passes for `13_margin`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: collapse adjacent vertical margins between stacked block
    siblings instead of summing both margins
- The same live geometry lane now passes for `14_border`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: confirms the corrected sibling vertical margin-collapse
    behavior also yields browser-matched stacked geometry when borders are
    present on the same fixture
- The same live geometry lane now passes for `16_flex_row`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: add a dedicated flex-column container layout path so flex
    item margins do not collapse like block siblings, while keeping the nested
    row container geometry browser-matched
- The same live geometry lane now passes for `17_flex_col`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: confirms the same dedicated flex-column container path also
    matches Chromium for the nested column-on-column case
