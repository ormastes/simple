# Chromium Geometry And Windows Native MDI Next Steps

Date: 2026-06-11

Scope:

- Windows-native MDI/titlebar/button/input/event verification
- Deeper Chromium geometry extraction for Simple layout comparison

## Current Verified State

- Linux Electron MDI evidence is live and passing through
  `scripts/check/check-electron-mdi-evidence.shs`.
- Windows-native MDI/titlebar evidence now has a dedicated wrapper/spec/probe
  lane (`scripts/check/check-windows-native-mdi-evidence.shs`,
  `test/03_system/gui/windows_native_mdi_evidence_spec.spl`,
  `src/os/hosted/hosted_win32_mdi_probe.spl`) but is still host-gated.
  The proof file now also requires `titlebar_css_present=true`, so the Win32
  hosted MDI lane checks the titlebar widget CSS contract in addition to the
  titlebar button, body button, text input, drag, focus, minimize, and restore
  fields.
  The Windows screenshot validator also counts custom titlebar CSS-colored
  pixels and the wrapper emits
  `windows_native_mdi_evidence_titlebar_css_pixels`, so the Windows pass lane
  requires rendered evidence of the styled titlebar widget colors.
  The probe additionally scans the Win32 hosted backend DIB after Simple Web
  rendering and emits
  `windows_native_mdi_evidence_rendered_titlebar_css_pixels`, tying the CSS
  proof to exact rendered compositor pixels instead of only source markup.
- macOS live-window evidence is still host-gated (`check-macos-gui-live-window-evidence.shs`),
  and this Linux host can only prove the explicit `requires-macos` skip lane.
  The macOS pass contract now includes rendered titlebar widget CSS pixel
  counts from the captured BMP (`titlebar_css_pixels`, widget fill, accent,
  and text counts) and fails on macOS if the fill/accent/text colors are absent.
- Current checked-in Chromium parity lane is still the older
  `src/app/wm_compare/html_compat.spl` bitmap/golden subset plus
  `structural_layout_report.spl`. The live Chrome structural geometry manifest
  now covers 50 labeled fixtures through `53_flex_wrap_align_content_flex_end` with exact
  geometry matches and `blur_or_tolerance_used=false`.

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

- The Windows-native wrapper/probe lane now exists but remains host-gated, so
  this Linux host still only verifies skip behavior (`requires-windows`).
- MDI/titlebar-specific live evidence is still being developed in a separate
  lane.
- The Win32 proof contract now includes `titlebar_css_present=true`. This is a
  source/probe contract check until the wrapper is run on a Windows host and
  captures live screenshot evidence.
- The live Windows screenshot validator now rejects captures that lack
  custom titlebar CSS color pixels. This remains host-gated: Linux still proves
  only the explicit `requires-windows` skip lane.
- The Win32 probe also records exact DIB pixels for the custom titlebar widget
  CSS colors inside the terminal content band. The wrapper requires
  `rendered_titlebar_css_applied=true` before reporting a Windows pass.

Smallest next implementation step:

1. Keep the existing host-gated Windows-native lane and wire its outputs into
   release evidence plumbing.
2. On Linux, continue to verify the explicit non-Windows/skip lane.
3. Finish the MDI/titlebar-specific live evidence in its separate lane while
   preserving this Chromium geometry lane focus.

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
- Live `18_flex_grow_weights` evidence now also passes with `layout_match` and
  `mismatch_count=0`.
- The focused weighted flex-grow fix was:
  - stop treating positive `flex` shorthand as a generic fill flag on the child
  - parse `flex` / `flex-grow` into an integer grow weight
  - distribute leftover row flex width by cumulative left-to-right weighted
    rounding so the single-pixel remainder lands on the same child Chromium
    chooses in this focused case
- Live `19_flex_shrink_weights` evidence now also passes with `layout_match`
  and `mismatch_count=0`.
- The focused weighted flex-shrink fix was:
  - add `flex-shrink` style state with default `1`
  - parse `flex-shrink` plus the second component of the `flex` shorthand
  - apply scaled shrink-factor distribution proportional to
    `flex-shrink * flex-base-size`, matching the Flexbox spec rule used by
    Chromium for this case
  - clamp explicit child width to the flex-resolved width passed down by the
    parent so the used main size, not the authored width, drives child geometry
  - preserve that shrink-resolved width in the final child box geometry instead
    of letting the child’s authored explicit width overwrite it during its own
    layout pass
- Live `20_flex_basis_override` evidence now also passes with `layout_match`
  and `mismatch_count=0`.
- The focused flex-basis fix was:
  - add `flex-basis` style state
  - parse both the explicit `flex-basis` property and the third component of
    the `flex` shorthand
  - use the flex basis as the item’s main-axis base size in row flex layout
  - let the child use the parent-resolved flex width instead of the authored
    `width` when flex basis overrides width
- Live `21_flex_wrap_basic` evidence now also passes with `layout_match`
  and `mismatch_count=0`.
- The focused flex-wrap fix was:
  - add `flex-wrap` style state and parse `flex-wrap: wrap`
  - add a wrapped row-flex path that starts a new flex line when the next
    item no longer fits the current line
  - accumulate container height from multiple wrapped lines instead of a single
    row max-height
- Live `25_flex_justify_space_between` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- Live `26_flex_gap_basic` evidence now passes with `layout_match` and
  `mismatch_count=0`.
- The focused fixture-26 fix was:
  - keep the real Chrome/default-body fixture rather than resetting body margin
  - collapse the first in-flow child top margin through the default body top
    margin when the body has no top border or padding
  - preserve exact row-flex gap positions (`x=24,76,138`) and match Chrome's
    y=16 top edge
- Live `27_absolute_position_basic` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-27 result records Chromium absolute-position behavior
  inside a padded, bordered `position:relative` containing block:
  - the parent border box is `x=24`, `y=16`, `width=184`, `height=114`
  - the absolute child border box is `x=46`, `y=33`, `width=40`, `height=24`
  - the result confirms the existing Simple absolute-position path matches
    Chrome for this case without using blur, tolerance, or copied pixels
- Live `28_display_contents_basic` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-28 result records Chromium `display:contents` behavior:
  - the `display:contents` wrapper is intentionally not labeled because Chrome
    does not generate a normal layout box for it
  - the section border box is `x=16`, `y=16`, `width=128`, `height=54`
  - the wrapper children flow directly under the section at
    `contents_first` `x=20`, `y=20`, `contents_second` `x=20`, `y=38`, and
    `contents_after` `x=20`, `y=56`
  - the result confirms Simple matches this focused contents-flow case without
    blur, tolerance, resolution scaling, or copied Chromium pixels
- Live `29_box_sizing_border_box` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-29 result records Chromium CSS box-sizing behavior:
  - the default content-box child border box is `x=20`, `y=20`, `width=110`,
    `height=50` from `width:80`, `height:20`, `padding:10`, and `border:5`
  - the `box-sizing:border-box` child border box is `x=20`, `y=76`,
    `width=80`, `height=40`, proving width/height include padding and border
  - the padded section border box is `x=16`, `y=16`, `width=228`,
    `height=104`
  - the result confirms Simple matches this focused CSS box model case without
    blur, tolerance, resolution scaling, or copied Chromium pixels
- Live `30_min_max_width_basic` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-30 result records Chromium min/max width behavior:
  - `width:50px; min-width:90px` produces a `90x20` border box
  - `width:140px; max-width:80px` produces an `80x20` border box
  - an auto-width block with `max-width:100px` clamps from the parent content
    width to a `100x20` border box
  - the padded section border box is `x=16`, `y=16`, `width=228`,
    `height=80`
  - the result confirms Simple matches this focused CSS width-constraint case
    without blur, tolerance, resolution scaling, or copied Chromium pixels
- Live `31_flex_align_items_center` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-31 result records Chromium row-flex cross-axis centering:
  - the explicit flex container border box is `x=16`, `y=16`, `width=220`,
    `height=80`
  - child heights `20`, `40`, and `28` are centered at `y=46`, `y=36`, and
    `y=42` respectively
  - the result confirms Simple matches this focused `align-items:center` case
    without blur, tolerance, resolution scaling, or copied Chromium pixels
- Live `32_flex_align_items_flex_end` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-32 result records Chromium row-flex cross-axis end
  alignment:
  - the explicit flex container border box is `x=16`, `y=16`, `width=220`,
    `height=80`
  - child heights `20`, `40`, and `28` are bottom-aligned inside the 80px
    content height at `y=76`, `y=56`, and `y=68` respectively
  - the result confirms Simple matches this focused `align-items:flex-end`
    case without blur, tolerance, resolution scaling, or copied Chromium
    pixels
- Live `33_flex_justify_flex_end` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-33 result records Chromium row-flex main-axis end
  alignment:
  - the explicit flex container border box is `x=16`, `y=16`, `width=220`,
    `height=60`
  - child widths `40`, `50`, and `30` are packed against the right content
    edge at `x=116`, `x=156`, and `x=206` respectively
  - the result confirms Simple matches this focused `justify-content:flex-end`
    case without blur, tolerance, resolution scaling, or copied Chromium
    pixels
- Live `34_flex_justify_center` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-34 result records Chromium row-flex main-axis centering:
  - the explicit flex container border box is `x=16`, `y=16`, `width=220`,
    `height=60`
  - child widths `40`, `50`, and `30` are centered as a 120px run inside the
    220px content width at `x=66`, `x=106`, and `x=156` respectively
  - the result confirms Simple matches this focused `justify-content:center`
    case without blur, tolerance, resolution scaling, or copied Chromium
    pixels
- Live `35_flex_align_items_stretch` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-35 result records Chromium row-flex cross-axis stretching:
  - the explicit flex container border box is `x=16`, `y=16`, `width=220`,
    `height=60`
  - auto-height child border boxes stretch to the 60px line cross size at
    `x=16`, `x=56`, and `x=106`
  - the Simple row-flex layout now applies a scoped used cross-size override
    for auto-height, non-absolute children when `align-items:stretch` has a
    definite container cross size
  - the result confirms Simple matches this focused `align-items:stretch`
    case without blur, tolerance, resolution scaling, or copied Chromium
    pixels
- Live `36_flex_align_self_flex_end` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-36 result records Chromium per-item row-flex cross-axis
  alignment:
  - the explicit flex container border box is `x=16`, `y=16`, `width=220`,
    `height=80`
  - the parent uses `align-items:flex-start`, while the middle child uses
    `align-self:flex-end` and moves to `x=56`, `y=56`, `width=50`,
    `height=40`
  - the Simple style model now parses and preserves `align-self`, and row-flex
    cross-axis placement resolves per-item alignment before center, flex-end,
    baseline, or stretch handling
  - the result confirms Simple matches this focused `align-self:flex-end`
    case without blur, tolerance, resolution scaling, or copied Chromium
    pixels
- Live `37_flex_gap_justify_center` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-37 result records Chromium row-flex main-axis centering
  when `gap` contributes to the centered run:
  - the explicit flex container border box is `x=16`, `y=16`, `width=220`,
    `height=60`
  - child widths `40`, `50`, and `30` with `gap:12px` form a 144px run
    centered at `x=54`, `x=106`, and `x=168`
  - the result confirms Simple matches this focused `gap` plus
    `justify-content:center` case without blur, tolerance, resolution scaling,
    or copied Chromium pixels
- Live `38_flex_gap_space_between` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-38 result records Chromium row-flex main-axis
  distribution when `gap` contributes a base interval and
  `justify-content:space-between` adds the remaining free space between items:
  - the explicit flex container border box is `x=16`, `y=16`, `width=220`,
    `height=60`
  - child widths `40`, `50`, and `30` with `gap:10px` leave 80px free; Chrome
    adds 40px to each inter-item gap, placing children at `x=16`, `x=106`,
    and `x=206`
  - the result confirms Simple matches this focused `gap` plus
    `justify-content:space-between` case without blur, tolerance, resolution
    scaling, or copied Chromium pixels
- Live `39_flex_gap_flex_end` evidence now passes with `layout_match` and
  `mismatch_count=0`.
- The focused fixture-39 result records Chromium row-flex main-axis placement
  when `gap` contributes to the run width and `justify-content:flex-end` shifts
  that whole run to the container end:
  - the explicit flex container border box is `x=16`, `y=16`, `width=220`,
    `height=60`
  - child widths `40`, `50`, and `30` with `gap:10px` form a 140px run; Chrome
    applies the remaining 80px as the start offset, placing children at
    `x=96`, `x=146`, and `x=206`
  - the result confirms Simple matches this focused `gap` plus
    `justify-content:flex-end` case without blur, tolerance, resolution
    scaling, or copied Chromium pixels
- Live `40_flex_column_gap_justify_center` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-40 result records Chromium column-flex main-axis
  centering when `gap` contributes to the vertical run:
  - the explicit flex container border box is `x=16`, `y=16`, `width=80`,
    `height=160`
  - child heights `30`, `40`, and `20` with two `10px` gaps form a 110px run;
    Chrome applies the remaining 50px as a 25px start offset, placing children
    at `y=41`, `y=81`, and `y=131`
  - the Simple column-flex branch now precomputes non-absolute child run
    height and applies `justify-content:center`, `flex-end`, and
    `space-between` main-axis offsets without blur, tolerance, resolution
    scaling, or copied Chromium pixels
- Live `41_flex_column_gap_space_between` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-41 result records Chromium column-flex main-axis
  distribution when `gap` contributes a base interval and
  `justify-content:space-between` adds the remaining free space between items:
  - the explicit flex container border box is `x=16`, `y=16`, `width=80`,
    `height=160`
  - child heights `30`, `40`, and `20` with `gap:10px` leave 50px free; Chrome
    adds 25px to each inter-item gap, placing children at `y=16`, `y=81`, and
    `y=156`
  - the result confirms the column-flex branch matches this focused
    `gap` plus `justify-content:space-between` case without blur, tolerance,
    resolution scaling, or copied Chromium pixels
- Live `42_flex_column_gap_flex_end` evidence now passes with `layout_match`
  and `mismatch_count=0`.
- The focused fixture-42 result records Chromium column-flex end placement when
  `gap` contributes to the vertical run:
  - the explicit flex container border box is `x=16`, `y=16`, `width=80`,
    `height=160`
  - child heights `30`, `40`, and `20` with two `10px` gaps form a 110px run;
    Chrome applies the remaining 50px as the start offset, placing children at
    `y=66`, `y=106`, and `y=156`
  - the result confirms the column-flex branch matches this focused
    `gap` plus `justify-content:flex-end` case without blur, tolerance,
    resolution scaling, or copied Chromium pixels
- Live `43_flex_column_align_items_center` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-43 result records Chromium column-flex cross-axis
  centering for fixed-width children:
  - the explicit flex container border box is `x=16`, `y=16`, `width=100`,
    `height=120`
  - child widths `40`, `60`, and `20` are centered at `x=46`, `x=36`, and
    `x=56` while vertical stacking remains at `y=16`, `y=36`, and `y=56`
  - the Simple column-flex branch now applies `align-items:center` and
    `flex-end` cross-axis offsets for fixed-width children without blur,
    tolerance, resolution scaling, or copied Chromium pixels
- Live `44_flex_column_align_items_flex_end` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-44 result records Chromium column-flex cross-axis
  flex-end alignment for fixed-width children:
  - the explicit flex container border box is `x=16`, `y=16`, `width=100`,
    `height=120`
  - child widths `40`, `60`, and `20` are right-aligned at `x=76`, `x=56`,
    and `x=96` while vertical stacking remains at `y=16`, `y=36`, and `y=56`
  - the result confirms the existing Simple column-flex `align-items:flex-end`
    branch without blur, tolerance, resolution scaling, or copied Chromium
    pixels
- Live `45_flex_column_align_self_flex_end` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-45 result records Chromium column-flex cross-axis
  `align-self:flex-end` override for one fixed-width child:
  - the explicit flex container border box is `x=16`, `y=16`, `width=100`,
    `height=120`
  - the parent uses `align-items:flex-start`; the middle child overrides with
    `align-self:flex-end` and moves to `x=56`, while siblings stay at `x=16`
  - the result confirms the Simple column-flex `flex_item_align` override path
    without blur, tolerance, resolution scaling, or copied Chromium pixels
- Live `46_flex_column_align_items_stretch` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-46 result records Chromium column-flex cross-axis
  stretch for auto-width children:
  - the explicit flex container border box is `x=16`, `y=16`, `width=100`,
    `height=120`
  - all three auto-width children stretch to `width=100` at `x=16` while
    vertical stacking remains at `y=16`, `y=36`, and `y=56`
  - the result confirms the existing Simple column-flex stretch/default-width
    path without blur, tolerance, resolution scaling, or copied Chromium pixels
- Live `47_flex_column_align_self_center` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-47 result records Chromium column-flex cross-axis
  `align-self:center` override for one fixed-width child:
  - the explicit flex container border box is `x=16`, `y=16`, `width=100`,
    `height=120`
  - the parent uses `align-items:flex-start`; the middle child overrides with
    `align-self:center` and moves to `x=36`, while siblings stay at `x=16`
  - the result confirms the Simple column-flex `flex_item_align` center
    override path without blur, tolerance, resolution scaling, or copied
    Chromium pixels
- Live `48_flex_column_align_self_stretch` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-48 result records Chromium column-flex cross-axis
  `align-self:stretch` override for one auto-width child:
  - the explicit flex container border box is `x=16`, `y=16`, `width=100`,
    `height=120`
  - the parent uses `align-items:flex-start`; the middle child overrides with
    `align-self:stretch` and stretches to `width=100`, while fixed-width
    siblings stay at `width=40` and `width=20`
  - the result confirms the Simple column-flex stretch override path without
    blur, tolerance, resolution scaling, or copied Chromium pixels
- Live `49_flex_column_justify_space_around` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-49 result records Chromium column-flex main-axis
  `justify-content:space-around` distribution:
  - the explicit flex container border box is `x=16`, `y=16`, `width=100`,
    `height=130`
  - child heights `20`, `30`, and `20` leave 60px free; Chrome applies 10px
    before the first item, 20px between items, and 10px after the last item,
    placing children at `y=26`, `y=66`, and `y=116`
  - the Simple column-flex branch now applies the same focused
    `space-around` start and gap distribution without blur, tolerance,
    resolution scaling, or copied Chromium pixels
- Live `50_flex_row_justify_space_around` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-50 result records Chromium row-flex main-axis
  `justify-content:space-around` distribution:
  - the explicit flex container border box is `x=16`, `y=16`, `width=130`,
    `height=80`
  - child widths `20`, `30`, and `20` leave 60px free; Chrome applies 10px
    before the first item, 20px between items, and 10px after the last item,
    placing children at `x=26`, `x=66`, and `x=116`
  - the Simple row-flex branch applies the same focused `space-around` start
    and gap distribution without blur, tolerance, resolution scaling, or
    copied Chromium pixels
- Live `51_flex_row_justify_space_evenly` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-51 result records Chromium row-flex main-axis
  `justify-content:space-evenly` distribution:
  - the explicit flex container border box is `x=16`, `y=16`, `width=130`,
    `height=80`
  - child widths `20`, `30`, and `20` leave 60px free; Chrome applies four
    equal 15px spaces, placing children at `x=31`, `x=66`, and `x=111`
  - the Simple row-flex branch applies the same focused `space-evenly` start
    and gap distribution without blur, tolerance, resolution scaling, or
    copied Chromium pixels
- Live `52_flex_column_justify_space_evenly` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-52 result records Chromium column-flex main-axis
  `justify-content:space-evenly` distribution:
  - the explicit flex container border box is `x=16`, `y=16`, `width=100`,
    `height=130`
  - child heights `20`, `30`, and `20` leave 60px free; Chrome applies four
    equal 15px spaces, placing children at `y=31`, `y=66`, and `y=111`
  - the Simple column-flex branch applies the same focused `space-evenly`
    start and gap distribution without blur, tolerance, resolution scaling, or
    copied Chromium pixels
- Live `53_flex_wrap_align_content_flex_end` evidence now passes with
  `layout_match` and `mismatch_count=0`.
- The focused fixture-53 result records Chromium row flex-wrap cross-axis
  `align-content:flex-end` distribution:
  - the explicit flex container border box is `x=16`, `y=16`, `width=90`,
    `height=120`
  - the two wrapped lines have heights `20` and `30`, leaving 70px free in the
    cross axis; Chrome places the first line at `y=86` and the second at
    `y=106`
  - the Simple row-wrap branch applies the same focused `flex-end` cross-axis
    offset without blur, tolerance, resolution scaling, or copied Chromium
    pixels
- Live `22_flex_align_items_baseline` evidence now also passes with
  `layout_match` and `mismatch_count=0`.
- The focused baseline-alignment fix was:
  - add `align-items` style state and parse `align-items: baseline`
  - stop treating plain auto-width text flex items as implicit grow items
  - estimate intrinsic text width for focused text-only flex items so sibling
    `x` positions match Chromium
  - apply a focused text-baseline offset in the row-flex path so the smaller
    item drops to Chromium’s baseline-aligned `y` position
  - attach focused text labels on the Simple side so the structured geometry
    report carries the same text evidence Chromium emits
- Live `23_flex_wrap_align_content_center` evidence now also passes with
  `layout_match` and `mismatch_count=0`.
- The focused multi-line align-content fix was:
  - add `align-content` style state and parse `align-content: center`
  - preserve explicit wrapped-container height instead of always collapsing to
    content height
  - precompute wrapped line heights and total multi-line content height
  - center the block of wrapped lines inside the explicit cross size for the
    focused `align-content:center` case
- Chrome headless manifest evidence now includes
  `25_flex_justify_space_between`, `26_flex_gap_basic`,
  `27_absolute_position_basic`, `28_display_contents_basic`, and
  `29_box_sizing_border_box`, `30_min_max_width_basic`,
  `31_flex_align_items_center`, `32_flex_align_items_flex_end`,
  `33_flex_justify_flex_end`, `34_flex_justify_center`, and
  `35_flex_align_items_stretch`, `36_flex_align_self_flex_end`, and
  `37_flex_gap_justify_center`, `38_flex_gap_space_between`,
  `39_flex_gap_flex_end`, `40_flex_column_gap_justify_center`,
  `41_flex_column_gap_space_between`, `42_flex_column_gap_flex_end`, and
  `43_flex_column_align_items_center`, and
  `44_flex_column_align_items_flex_end`, and
  `45_flex_column_align_self_flex_end`, and
  `46_flex_column_align_items_stretch`, and
  `47_flex_column_align_self_center`, and
  `48_flex_column_align_self_stretch`, and
  `49_flex_column_justify_space_around`, and
  `50_flex_row_justify_space_around`, and
  `51_flex_row_justify_space_evenly`, and
  `52_flex_column_justify_space_evenly`, and
  `53_flex_wrap_align_content_flex_end`:
  - `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
    covers fixtures `02` through `53` in its default manifest, excluding only
    the older text-only starter fixtures
  - `doc/09_report/chrome_html_compat_geometry_manifest_evidence_2026-06-11.md`
    reports `50` fixtures, `50` passes, `0` failures, and
    `blur_or_tolerance_used=false`
  - `tools/chrome-live-bitmap/capture_html_argb.js` now waits briefly for the
    Chrome DevTools page target after launch, avoiding a startup race without
    changing geometry comparison semantics
  - `html_compat_spec.spl` now guards the wrapper/capture source against
    geometry acceptance through `argb_json`, pixelmatch, resize/scale/blur,
    canvas, threshold, or image-smoothing shortcuts
- Live `24_flex_wrap_reverse_basic` evidence now also passes with
  `layout_match` and `mismatch_count=0`.
- The focused geometry spec itself is now stable again in the default runner:
  - `simple test test/03_system/gui/wm_compare/html_compat_geometry_probe_spec.spl`
    passes after restructuring the spec into helper functions invoked from a
    single `it`, which avoids the earlier runner state corruption across many
    separate examples.
- Native/default evidence is split:
  - `simple test test/03_system/gui/wm_compare/html_compat_geometry_probe_spec.spl --json --no-cache`
    passes with one scenario and zero failures.
  - `simple test test/03_system/gui/wm_compare/html_compat_geometry_probe_spec.spl --mode=native --json --no-cache`
    still reports one failed file without detailed assertion output.
  - a standalone native smoke binary proves the renderer-backed closure can
    be built and entered without `spl_*`, `json_deep_equals`, or spec-runtime
    BDD symbols:
    - entry: `src/app/wm_compare/html_compat_geometry_probe_native_smoke.spl`
    - build: `simple native-build ... --entry src/app/wm_compare/html_compat_geometry_probe_native_smoke.spl`
    - after fixing the stale `TextRenderCache.char_w` debug-field reference
      and the Cranelift text `.len()` fast path, the build completes with
      `0 failed` and no generated renderer stubs
    - artifact contains `simple_web_layout_render_html_draw_ir`; it has no
      `spl_dlopen`, `spl_dlsym`, `spl_dlclose`, `spl_wffi_call_i64`,
      `json_deep_equals`, or `rt_bdd_expect_eq_rv`
    - `parse_html` no longer uses native `spl_array_pop` for closing-tag stack
      truncation
    - the standalone binary now runs with `status=pass`, `box_count=4`
  - a fixture-24 native full smoke at
    `src/app/wm_compare/html_compat_geometry_probe_native_full_smoke.spl`
    now builds with `0 failed` and runs with
    `fixture=24_flex_wrap_reverse_basic count=4`, `status=pass`
  - the core-C native runtime now exports `rt_file_read_text_rv`, and the
    diagnostic native file-read smoke passes, so the earlier file-read ABI
    blocker is closed.
  - native file-backed full-spec proof remains incomplete: the latest
    reduction fixed the native zero-command path for `04_button` and
    `05_text_input` by consuming non-rendered head metadata before parser arena
    insertion, but `06_card_panel` still returns zero boxes natively for the
    multi-text block case; the SSpec now guards that length before indexing so
    the lane fails honestly instead of dereferencing missing boxes.
  - live Electron wrapper evidence for fixture `24_flex_wrap_reverse_basic`
    is green again after fixing closing-tag stack truncation:
    `scripts/check/check-electron-html-compat-geometry-evidence.shs` reports
    `layout_match`, `mismatch_count=0`.
- Additional fixture-24 hardening:
  - Electron geometry JSON extraction has a focused fallback for pretty CDP
    output, so the live report no longer parses as zero boxes.
  - CSS numeric parsing now uses explicit digit matching.
  - renderer layout calls now pass separate x/y/w/h arrays instead of aliasing
    one zero array, which had collapsed distinct geometry fields together.
- The focused wrap-reverse fix was:
  - extend `flex-wrap` from a boolean to a mode: `nowrap`, `wrap`,
    `wrap-reverse`
  - place wrapped flex lines from the opposite cross-axis edge for
    `wrap-reverse`
  - compute wrapped container height from the total stacked line height instead
    of the last line anchor position
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
  - the focused weighted row flex-grow distribution gap for
    `18_flex_grow_weights` is also closed in the same live lane
  - the focused weighted row flex-shrink distribution gap for
    `19_flex_shrink_weights` is also closed in the same live lane
  - the focused row flex-basis-overrides-width gap for
    `20_flex_basis_override` is also closed in the same live lane
  - the focused wrapped row flex-line break and multi-line height gap for
    `21_flex_wrap_basic` is also closed in the same live lane
  - the focused row flex baseline-alignment gap for
    `22_flex_align_items_baseline` is also closed in the same live lane
  - the focused multi-line wrapped flex cross-axis packing gap for
    `23_flex_wrap_align_content_center` is also closed in the same live lane
  - the focused wrap-reverse line-order gap for
    `24_flex_wrap_reverse_basic` is also closed in the same live lane
  - broader geometry parity is still incomplete; this is one verified case, not
    completion of the full layout objective

## This Turn's Code Increment

The in-repo Chromium devtools mirror/session now has a geometry storage hook:

- `src/app/ui.chromium.devtools/dom_mirror.spl`
- `src/app/ui.chromium.devtools/attach_session.spl`

This is only storage, not live CDP extraction yet. It gives the Chromium lane
an in-tree destination for per-node bounds before wiring a browser-side
extractor.
