# Simple Browser Chromium HTML Parity System Test Plan

Feature: `simple_browser_chromium_html_parity`

Current state as of 2026-06-11:

- The authoritative current pixel harness in this worktree is
  `src/app/wm_compare/html_compat.spl`, now covering fixtures `00..07`, CSS
  layers `10..17`, and flex rows `18..24`.
- The newer focused fixture lane described in some earlier progress notes
  (`146+`, client-rect/box-model parity rows, no-cheat guard summaries) is not
  present in the current worktree and must not be treated as current evidence.
- Current checked-in parity scope is still a mixed bitmap/golden lane. It is
  useful for regression pressure, but it is not yet broad Chromium layout-engine
  parity. Exact Chrome/Simple pixel rows now exist for flex fixtures 18, 19,
  20, 21, 23, and 24; fixture 22 remains blocked by text glyph raster/default
  font differences.
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
- `SIMPLE_BINARY=<release-simple> bin/simple run src/app/wm_compare/html_compat.spl --only=19_flex_shrink_weights --update-baseline --simple-timeout-ms=1000`
- `SIMPLE_BINARY=<release-simple> bin/simple run src/app/wm_compare/html_compat.spl --only=20_flex_basis_override --update-baseline --simple-timeout-ms=1000`
- `SIMPLE_BINARY=<release-simple> bin/simple run src/app/wm_compare/html_compat.spl --only=21_flex_wrap_basic --update-baseline --simple-timeout-ms=1000`
- `SIMPLE_BINARY=<release-simple> bin/simple run src/app/wm_compare/html_compat.spl --only=23_flex_wrap_align_content_center --update-baseline --simple-timeout-ms=1000`
- `SIMPLE_BINARY=<release-simple> bin/simple run src/app/wm_compare/html_compat.spl --only=24_flex_wrap_reverse_basic --update-baseline --simple-timeout-ms=1000`

Regression checks:

- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
- `bin/simple test test/03_system/wm_compare/html_compat_spec.spl`
- `bin/simple test test/03_system/wm_compare/golden_gate_spec.spl`

Open gaps tied to the active browser objective:

- No current checked-in focused fixture lane for deeper flex/grid/LayoutNG-style
  geometry comparison.
- No current direct Chromium layout extraction/access path in this worktree.
- Pixel rows for `19_flex_shrink_weights`, `20_flex_basis_override`,
  `21_flex_wrap_basic`, `23_flex_wrap_align_content_center`, and
  `24_flex_wrap_reverse_basic` now write real Chrome and Simple P6 PPMs through
  live Chromium capture plus the Simple software layout renderer and compare
  byte-identical. Fixture `22_flex_align_items_baseline` writes both PPMs but
  remains uncommitted as an accepted row because the text glyph area differs by
  475 pixels after aligning the default text color with Chromium black; exact
  completion requires browser-like font metrics, raster, and antialiasing
  rather than tolerance or copied browser pixels.
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
- The same live geometry lane now passes for `18_flex_grow_weights`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: parse `flex` / `flex-grow` into integer grow weights and
    distribute leftover row flex width with weighted cumulative rounding so the
    single-pixel remainder matches Chromium
- The same live geometry lane now passes for `19_flex_shrink_weights`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: parse `flex-shrink` and the second `flex` shorthand component,
    distribute negative free space by scaled shrink factors, and preserve the
    flex-resolved child width instead of letting the authored explicit width
    overwrite the final box geometry
- The same live geometry lane now passes for `20_flex_basis_override`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: parse `flex-basis` plus the third `flex` shorthand component,
    use flex basis as the main-axis base size, and let it override authored
    width in the child’s used geometry
- The same live geometry lane now passes for `21_flex_wrap_basic`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: parse `flex-wrap: wrap`, start a new row when the next item no
    longer fits the current line, and accumulate container height across
    multiple flex lines
- The same live geometry lane now passes for `22_flex_align_items_baseline`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: parse `align-items: baseline`, keep plain text flex items at
    intrinsic width instead of implicit grow width, and apply a focused
    baseline offset for row-flex text items, plus focused text-label mapping on
    the Simple side
- The same live geometry lane now passes for `23_flex_wrap_align_content_center`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: parse `align-content: center`, keep explicit multi-line flex
    container height, precompute wrapped line heights, and center the block of
    flex lines within the container’s cross size
- The same live geometry lane now passes for `24_flex_wrap_reverse_basic`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: treat `flex-wrap` as a mode instead of a boolean, place
    wrapped lines from the opposite cross-axis edge for `wrap-reverse`, and
    compute the container height from total stacked line height
- The focused geometry spec file is green in the default no-cache runner:
  - `simple test test/03_system/gui/wm_compare/html_compat_geometry_probe_spec.spl --json --no-cache`
    passes with one listed scenario and zero failures
- Native executable smoke is green, but native no-cache spec mode remains red:
  - the standalone native smoke at
    `src/app/wm_compare/html_compat_geometry_probe_native_smoke.spl` builds
    with `0 failed` and runs with `status=pass`, `box_count=4`
  - the fixture-24 native full smoke at
    `src/app/wm_compare/html_compat_geometry_probe_native_full_smoke.spl`
    builds with `0 failed` and runs with
    `fixture=24_flex_wrap_reverse_basic count=4`, `status=pass`
  - `simple test test/03_system/gui/wm_compare/html_compat_geometry_probe_spec.spl --mode=native --json --no-cache`
    still reports one failed file without an assertion detail
  - the core-C native runtime now exports `rt_file_read_text_rv`, and the
    diagnostic native file-read smoke passes, so the earlier file-read ABI
    blocker is closed
  - the latest reduction found a native renderer divergence before fixture 24:
    full-document metadata parsing (`head` + `meta` + `title`) made native
    `04_button`/`05_text_input` return zero Draw IR commands; the parser now
    consumes non-rendered metadata before arena insertion, and the native
    staged probe reaches `06_card_panel`
  - broad native SSpec mode remains red: `06_card_panel` still returns zero
    boxes natively for the multi-text block case, and the full native runner
    reports one failed file / timeout-style failure rather than proving parity
  - fixes that moved this forward:
    - Cranelift inline `.len()` now recognizes runtime string values instead
      of returning the tagged `-1` sentinel for text
    - `parse_html` no longer uses `pstack.pop()` for closing-tag stack
      truncation, avoiding the native `spl_array_pop` crash
    - structural box extraction uses indexed lookup instead of optional
      command binding in the native smoke path
    - Electron geometry JSON extraction has a focused fallback for pretty
      CDP output, so fixture-24 no longer parses as zero boxes
    - CSS numeric parsing now uses explicit digit matching, and the renderer
      uses separate x/y/w/h layout arrays instead of aliasing one zero array
    - non-rendered head metadata is consumed before parser arena insertion,
      fixing the native zero-command path for `04_button` and `05_text_input`
    - the executable spec now guards `06_card_panel` length before indexing,
      so native evidence can fail honestly instead of dereferencing missing
      boxes
  - live Electron wrapper evidence is green again for
    `24_flex_wrap_reverse_basic` after fixing closing-tag stack truncation:
    `scripts/check/check-electron-html-compat-geometry-evidence.shs` reports
    `layout_match`, `mismatch_count=0`
