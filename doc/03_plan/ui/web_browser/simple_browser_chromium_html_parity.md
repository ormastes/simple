# Simple Browser Chromium HTML Parity System Test Plan

Feature: `simple_browser_chromium_html_parity`

Current state as of 2026-06-11:

- The authoritative current pixel harness in this worktree is
  `src/app/wm_compare/html_compat.spl`, now covering fixtures `00..07`, CSS
  layers `10..17`, flex rows `18..26`, absolute positioning fixture `27`, and
  display-contents fixture `28`, box-sizing fixture `29`, min/max-width
  fixture `30`, flex cross-axis centering fixture `31`, flex cross-axis
  end-alignment fixture `32`, flex main-axis end-alignment fixture `33`, flex
  main-axis centering fixture `34`, flex cross-axis stretch fixture `35`,
  per-item flex cross-axis alignment fixture `36`, and centered flex gap
  fixture `37`.
- The newer focused fixture lane described in some earlier progress notes
  (`146+`, client-rect/box-model parity rows, no-cheat guard summaries) is not
  present in the current worktree and must not be treated as current evidence.
- Current checked-in parity scope is still a mixed bitmap/golden lane. It is
  useful for regression pressure, but it is not yet broad Chromium layout-engine
  parity. Exact Chrome/Simple pixel rows now exist for flex fixtures 18, 19,
  20, 21, 23, 24, and 25; fixture 22 remains blocked by text glyph
  raster/default font differences.
- Important live-run caveat: the current CLI catalog reports 25 fixtures and
  `test/09_baselines/html_compat/18_flex_grow_weights/report.sdn` contains an
  exact checked-in row, but a fresh live source-B run on 2026-06-11 still times
  out:
  `SIMPLE_LIB=src bin/simple run src/app/wm_compare/html_compat.spl --only=18_flex_grow_weights`
  exits `2` with `timed out after 20000 ms while rendering source B in child process`.
  Direct worker execution renders fixture 18 in about `0.65s`, and the parent
  harness passes in about `2.3s` when `SIMPLE_BINARY` points to the active
  compiler, so the remaining blocker is automatic child-runtime discovery in
  isolated/checker environments. Do not treat the checked-in fixture-18 pixel
  row as portable live end-to-end proof until that runtime-selection issue is
  fixed without bypassing pure Simple layout/raster logic.
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
- Pixel fixture `18_flex_grow_weights` has checked-in exact PPMs and report
  metadata, and it passes the live parent harness when `SIMPLE_BINARY` is set
  to the active compiler. The same run currently times out when automatic child
  runtime discovery falls through in clean/isolated worktrees. This is tracked
  separately as
  `doc/08_tracking/bug/html_compat_fixture18_live_source_b_timeout_2026-06-11.md`.
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
  - evidence update: Chromium/Electron geometry capture now carries computed
    text/style metadata (`display`, `align-items`, `font-size`,
    `line-height`, `font-family`, `font-weight`, and `color`) in the structural
    box report. This records the browser text stack behind the remaining
    fixture-22 pixel blocker without treating font rasterization as solved.
    The same evidence now also records subpixel client rects (`rect_left`,
    `rect_top`, `rect_width`, and `rect_height`) alongside rounded integer
    geometry, exposing Chromium's exact box boundaries for follow-up layout
    parity work without changing the integer geometry comparison gate.
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
- The same live geometry lane now passes for `25_flex_justify_space_between`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: confirms the row-flex free-space distribution path matches
    Chromium's `justify-content: space-between` geometry for the fixture
- The same live geometry lane now passes for `26_flex_gap_basic`:
  - result: `layout_match`, `mismatch_count=0`
  - focused fix: preserve the existing row-flex `gap` spacing and add
    Chromium-like first-child top margin collapse through the default `body`
    margin, matching Chrome's y=16 top edge without resetting body margin
  - evidence update: `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    now reports `fixture_count=23`, `pass_count=23`, `fail_count=0`, and
    `blur_or_tolerance_used=false`
- The same live geometry lane now passes for `27_absolute_position_basic`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's absolute-position geometry inside a
    padded, bordered `position:relative` containing block; the child border box
    lands at `x=46`, `y=33`, matching the existing Simple path exactly
- The same live geometry lane now passes for `28_display_contents_basic`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's `display:contents` behavior without
    treating the wrapper as a generated layout box; the wrapper children flow
    directly under the padded section at `y=20`, `y=38`, and `y=56`
- The same live geometry lane now passes for `29_box_sizing_border_box`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's content-box versus `box-sizing:border-box`
    geometry in one fixture; the content-box child expands to `110x50`, while
    the border-box child stays at authored `80x40`
- The same live geometry lane now passes for `30_min_max_width_basic`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's min/max width constraints for explicit
    and auto-width blocks; widths clamp to `90`, `80`, and `100` CSS pixels
- The same live geometry lane now passes for `31_flex_align_items_center`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's `align-items:center` cross-axis offsets
    for row-flex children with heights `20`, `40`, and `28`
- The same live geometry lane now passes for `32_flex_align_items_flex_end`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's `align-items:flex-end` cross-axis offsets
    for row-flex children with heights `20`, `40`, and `28`
- The same live geometry lane now passes for `33_flex_justify_flex_end`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's `justify-content:flex-end` main-axis
    offsets for row-flex children with widths `40`, `50`, and `30`
- The same live geometry lane now passes for `34_flex_justify_center`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's `justify-content:center` main-axis offsets
    for row-flex children with widths `40`, `50`, and `30`
- The same live geometry lane now passes for `35_flex_align_items_stretch`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's `align-items:stretch` cross-axis sizing
    for auto-height row-flex children in a definite-height container
- The same live geometry lane now passes for `36_flex_align_self_flex_end`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's `align-self:flex-end` override for one
    row-flex child inside a parent using `align-items:flex-start`
- The same live geometry lane now passes for `37_flex_gap_justify_center`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's centered row-flex run when `gap:12px`
    contributes to the run width
- The same live geometry lane now passes for `38_flex_gap_space_between`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's row-flex distribution when `gap:10px`
    contributes a base interval and `justify-content:space-between` adds the
    remaining 40px to each inter-item gap
- The same live geometry lane now passes for `39_flex_gap_flex_end`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's row-flex end placement when `gap:10px`
    contributes to the run width and `justify-content:flex-end` applies the
    remaining 80px as the start offset
- The same live geometry lane now passes for `40_flex_column_gap_justify_center`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's column-flex centering when `gap:10px`
    contributes to the vertical run and `justify-content:center` applies a
    25px start offset
  - renderer update: the Simple column-flex path now precomputes the
    non-absolute child run height and applies main-axis free space for
    `center`, `flex-end`, and `space-between`
- The same live geometry lane now passes for `41_flex_column_gap_space_between`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's column-flex gap distribution when
    `justify-content:space-between` adds 25px to each inter-item gap
- The same live geometry lane now passes for `42_flex_column_gap_flex_end`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's column-flex end placement when `gap:10px`
    contributes to the vertical run and `justify-content:flex-end` applies a
    50px start offset
- The same live geometry lane now passes for `43_flex_column_align_items_center`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's column-flex cross-axis centering for
    fixed-width children
  - renderer update: the Simple column-flex path now applies
    `align-items:center` and `flex-end` cross-axis offsets for fixed-width
    children
- The same live geometry lane now passes for `44_flex_column_align_items_flex_end`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's column-flex cross-axis flex-end alignment
    for fixed-width children
  - renderer update: no new renderer change was needed beyond the existing
    column-flex `align-items:flex-end` branch
- The same live geometry lane now passes for `45_flex_column_align_self_flex_end`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's column-flex `align-self:flex-end`
    override for one fixed-width child while siblings remain flex-start
  - renderer update: no new renderer change was needed beyond the existing
    `flex_item_align` override path
- The same live geometry lane now passes for `46_flex_column_align_items_stretch`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's column-flex cross-axis stretch for
    auto-width children
  - renderer update: no new renderer change was needed beyond the existing
    column-flex default-width stretch path
- The same live geometry lane now passes for `47_flex_column_align_self_center`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's column-flex `align-self:center` override
    for one fixed-width child while siblings remain flex-start
  - renderer update: no new renderer change was needed beyond the existing
    `flex_item_align` center override path
- The same live geometry lane now passes for `48_flex_column_align_self_stretch`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's column-flex `align-self:stretch`
    override for one auto-width child while fixed-width siblings remain
    flex-start
  - renderer update: no new renderer change was needed beyond the existing
    column-flex stretch/default-width path
- The same live geometry lane now passes for `49_flex_column_justify_space_around`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's column-flex
    `justify-content:space-around` start and inter-item gap distribution
  - renderer update: the Simple column-flex main-axis path now applies
    focused `space-around` start and gap offsets
  - evidence update: `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    now reports `fixture_count=46`, `pass_count=46`, `fail_count=0`, and
    `blur_or_tolerance_used=false`
- The same live geometry lane now passes for `50_flex_row_justify_space_around`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's row-flex `justify-content:space-around`
    start and inter-item gap distribution
  - renderer update: no new renderer change was needed beyond the existing
    row-flex `space-around` parser and main-axis path
  - evidence update: `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    now reports `fixture_count=47`, `pass_count=47`, `fail_count=0`, and
    `blur_or_tolerance_used=false`
- The same live geometry lane now passes for `51_flex_row_justify_space_evenly`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's row-flex `justify-content:space-evenly`
    equal start, inter-item, and end spacing
  - renderer update: the Simple row/column flex main-axis path now parses and
    applies focused `space-evenly` start and gap offsets
  - evidence update: `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    now reports `fixture_count=48`, `pass_count=48`, `fail_count=0`, and
    `blur_or_tolerance_used=false`
- The same live geometry lane now passes for `52_flex_column_justify_space_evenly`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's column-flex `justify-content:space-evenly`
    equal start, inter-item, and end spacing
  - renderer update: no new renderer change was needed beyond the existing
    column-flex `space-evenly` parser and main-axis path
  - evidence update: `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    now reports `fixture_count=49`, `pass_count=49`, `fail_count=0`, and
    `blur_or_tolerance_used=false`
- The same live geometry lane now passes for `53_flex_wrap_align_content_flex_end`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's row flex-wrap `align-content:flex-end`
    cross-axis offset for a fixed-height container
  - renderer update: the Simple row-wrap branch now applies focused
    `align-content:flex-end` offset when explicit cross-axis space remains
  - evidence update: `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    now reports `fixture_count=50`, `pass_count=50`, `fail_count=0`, and
    `blur_or_tolerance_used=false`
- The same live geometry lane now passes for `54_flex_wrap_align_content_space_between`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's row flex-wrap
    `align-content:space-between` inter-line gap for a fixed-height container
  - renderer update: the Simple row-wrap branch now applies focused
    `align-content:space-between` line-gap distribution
  - evidence update: `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    now reports `fixture_count=51`, `pass_count=51`, `fail_count=0`, and
    `blur_or_tolerance_used=false`
- The same live geometry lane now passes for `55_flex_wrap_align_content_space_around`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's row flex-wrap
    `align-content:space-around` start offset and inter-line gap
  - renderer update: the Simple row-wrap branch now applies focused
    `align-content:space-around` offset and line-gap distribution
  - evidence update: `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    now reports `fixture_count=52`, `pass_count=52`, `fail_count=0`, and
    `blur_or_tolerance_used=false`
- The same live geometry lane now passes for `56_flex_wrap_align_content_space_evenly`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's row flex-wrap
    `align-content:space-evenly` start offset and inter-line gap
  - renderer update: the Simple row-wrap branch now applies focused
    `align-content:space-evenly` offset and line-gap distribution
  - evidence update: `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    now reports `fixture_count=53`, `pass_count=53`, `fail_count=0`, and
    `blur_or_tolerance_used=false`
- The same live geometry lane now passes for `57_flex_wrap_gap_basic`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's row flex-wrap `gap:8px` distribution
    across both item and line placement
  - evidence update: `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    now reports `fixture_count=54`, `pass_count=54`, `fail_count=0`, and
    `blur_or_tolerance_used=false`
- The same live geometry lane now passes for `58_flex_wrap_axis_gap_basic`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's row flex-wrap `column-gap:10px` and
    `row-gap:8px` axis-specific placement
  - renderer update: the Simple flex layout style model now keeps row and
    column gap values separately while preserving `gap` shorthand behavior
  - evidence update: `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    now reports `fixture_count=55`, `pass_count=55`, `fail_count=0`, and
    `blur_or_tolerance_used=false`
- The same live geometry lane now passes for `59_flex_column_axis_gap_basic`:
  - result: `layout_match`, `mismatch_count=0`
  - focused result: records Chrome's column flex `row-gap:10px` main-axis
    spacing while `column-gap:6px` does not move a single column
  - evidence update: `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    now reports `fixture_count=56`, `pass_count=56`, `fail_count=0`, and
    `blur_or_tolerance_used=false`
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
- Source-B child runtime discovery now fails fast instead of timing out in
  isolated worktrees:
  - `src/app/wm_compare/html_compat_part1.spl` and
    `src/app/wm_compare/site_corpus_compat.spl` validate configured/local
    Simple child candidates with a bounded `--version` probe before launching
    the render worker
  - `SIMPLE_BINARY=/home/ormastes/dev/pub/simple/bin/simple ... html_compat.spl
    --only=18_flex_grow_weights` still reports `RESULT: EXACT match`,
    `different_pixels=0`, with no blur/tolerance/resolution workaround
  - the same isolated worktree command without a runnable local child runtime
    exits in under a second with `no runnable Simple binary found for source B
    child; set SIMPLE_BINARY to the active runtime`
  - `site_corpus_compat.spl --only=site_0_google` has the same fast-fail guard
    for its bounded source-B watchdog path
- Famous-site corpus verification now uses the canonical checked-in baseline
  location consistently:
  - Node corpus tools and the SSpec manual/spec now point at
    `test/09_baselines/famous_site_corpus`, matching
    `src/app/wm_compare/site_corpus.spl`
  - existing corpus `report.sdn`, `report.production.sdn`, and manifest
    metadata paths were migrated from the stale `test/baselines/...` location
    without changing PPM pixels or Chromium metrics
  - `simple test test/03_system/gui/wm_compare/famous_site_corpus_spec.spl
    --mode=interpreter --clean --format json` now reports `45` passed and `0`
    failed
  - `verify_famous_site_corpus_completion.js` reports `STATUS: PASS`,
    `reportCount=132`, `checkedPixelReportCount=132`, and
    `computedMismatchCount=0`
  - `verify_famous_site_production_probe.js --sample=site_0_google` reports
    `STATUS: PASS` while preserving the honest production glyph/compositing
    divergence: `differentPixels=2717`, `computedDifferentPixels=2717`, and
    `chromeGlyphCompositingParity=false`
- Shared MDI titlebar widget evidence now locks down the backend-neutral
  titlebar control contract:
  - `ui_shared_mdi_titlebar_widget_spec.spl` asserts the exact titlebar button
    markup, including `class="simple-titlebar-widget"`,
    `data-simple-titlebar-widget="button"`, the routed `data-action`, and
    `type="button"` so the titlebar control cannot regress into an implicit
    form submit or body-only button
  - the same spec asserts the flex titlebar widget container CSS and the custom
    titlebar widget color CSS used by the shared renderer source
  - live Linux Electron evidence remains green through
    `wm_browser_event_routing_evidence_spec.spl`, which passed `3/3` and
    verifies titlebar drag/maximize routing, title command routing, titlebar
    text input traffic, body input events, traffic-button computed styles, and
    `blur_or_tolerance_used=false`
- Full famous-site div-geometry evidence is no longer chunk-only in the current
  runtime:
  - `site_corpus_div_geometry_summary_cli.spl 0 0 160 120 ... 132` passes in a
    single Simple process with `selected=132`, `matched=132`, `mismatched=0`,
    and `missing_metrics=0`
  - `structural_layout_report_spec.spl` now includes a regression scenario for
    `build_site_corpus_div_geometry_summary(0, 160, 120)`, covering the
    all-row aggregate API that previously had a segfault tracker
  - the chunked wrapper remains a fallback diagnostic, but
    `doc/09_report/famous_site_corpus_div_geometry_full_2026-06-11.md` is the
    current single-command evidence; it uses no blur, tolerance, downscaling,
    copied Chromium pixels, or text antialiasing normalization
- macOS MDI live-window evidence is now MDI-specific while remaining honestly
  host-gated:
  - `scripts/check/check-macos-gui-live-window-evidence.shs` launches
    `src/app/ui_shared_mdi/main.spl` by default instead of the generic GUI
    sample
  - `src/app/ui_shared_mdi/titlebar_contract_probe.spl` emits source-contract
    fields for the shared MDI titlebar button, body button, text input, and
    custom titlebar CSS
  - the macOS capture wrapper now converts the captured window PNG to BMP and
    emits rendered titlebar widget CSS pixel counts:
    `macos_gui_live_window_evidence_titlebar_css_pixels`,
    `macos_gui_live_window_evidence_titlebar_widget_fill_pixels`,
    `macos_gui_live_window_evidence_titlebar_widget_accent_pixels`, and
    `macos_gui_live_window_evidence_titlebar_widget_text_pixels`
  - on a real macOS pass, the wrapper fails if the titlebar widget fill,
    accent, or text CSS colors are missing from the capture; on Linux these
    fields stay zero and the lane remains an explicit `requires-macos` skip
  - `macos_gui_live_window_evidence_spec.spl` checks those MDI contract fields
    in both lanes, while Linux still reports only
    `macos_gui_live_window_evidence_status=skip` and
    `reason=requires-macos` for the live macOS window/capture evidence
- Windows native MDI evidence now requires the same titlebar CSS source
  contract in its host-gated proof file:
  - `src/os/hosted/hosted_win32_mdi_probe.spl` emits
    `titlebar_css_present=true` when the terminal MDI HTML contains the shared
    flex titlebar widget container CSS and the custom titlebar widget color CSS
  - `scripts/check/check-windows-native-mdi-evidence.shs` and
    `windows_native_mdi_evidence_spec.spl` fail the Windows pass lane if that
    field is missing; on Linux this still only proves the explicit
    `requires-windows` skip path
  - the Win32 live screenshot validator also requires
    `titlebar_css_pixels > 19` for the custom titlebar widget green colors and
    the wrapper exposes that as
    `windows_native_mdi_evidence_titlebar_css_pixels`
  - the Win32 hosted probe scans the compositor DIB after Simple Web rendering
    and requires `rendered_titlebar_css_applied=true`, exposing the exact
    rendered count as
    `windows_native_mdi_evidence_rendered_titlebar_css_pixels`
- Flex main-axis distribution now has a Chromium-captured fixture:
  - added `25_flex_justify_space_between` to the HTML compatibility catalog
    and structural geometry probe
  - `simple_web_html_layout_renderer.spl` parses `justify-content` and applies
    row-flex positive free-space distribution for `space-between`, `center`,
    and end alignment when flex-grow/shrink are not consuming the line space
  - live Electron geometry evidence for fixture 25 reports `layout_match` with
    `mismatch_count=0`
  - live Chrome headless geometry manifest evidence now includes fixture 25:
    `chrome_html_compat_geometry_manifest_evidence_2026-06-11.md` reports
    `22` fixtures, `22` passes, `0` failures, and
    `blur_or_tolerance_used=false`
  - `html_compat_spec.spl` now includes a source-level no-cheat guard for the
    Chrome geometry manifest wrapper and capture tool, requiring geometry JSON
    to feed the structural probe and rejecting resize/scale/blur/filter,
    pixelmatch, canvas, threshold, or image-smoothing shortcuts
  - the fixture has real `chrome.ppm` captured via the existing Electron
    `--update-baseline --skip-simple` path, and the follow-up Simple comparison
    reports `RESULT: EXACT match`, `different_pixels=0`; no blur, tolerance,
    copied Simple pixels, or resolution adjustment was used
- Native focused geometry evidence now executes past the previous text-method
  lowering blocker:
  - `html_compat_geometry_probe_native_full_smoke.spl` now checks both
    `06_card_panel` and `24_flex_wrap_reverse_basic`
  - interpreter mode for that smoke reports `fixture=06_card_panel count=3`,
    `fixture=24_flex_wrap_reverse_basic count=4`, and `status=pass`
  - native compilation no longer fails first on the local iterable loops in the
    focused renderer/probe/Draw IR closure; the `parse_html()` close-tag stack
    path also avoids `pstack.pop()` by copying the kept stack prefix
  - the Rust seed LLVM builtin-method path now maps `String.substring` to the
    existing `rt_slice` runtime instead of nonexistent `rt_string_substring`;
    the Pure Simple MIR lowering mirrors typed `text.substring` / `text.slice`
    to native string slice calls
  - rebuilt bootstrap compiler evidence:
    `compile html_compat_geometry_probe_native_full_smoke.spl --native` emits
    the native binary, and running it prints `status=pass`
  - this proves the focused native geometry smoke executes; it does not prove
    full Chromium layout parity, macOS live-window evidence, or Windows host
    evidence for the broader objective
