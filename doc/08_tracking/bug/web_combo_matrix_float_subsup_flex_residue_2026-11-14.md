# Web renderer: residue found while fixing floats, sub/sup and flex-grow

Found 2026-11-14 with the combination matrix
(`sh scripts/check/check-web-combo-matrix-chrome.shs`, Chrome 159.0.8154.6,
Linux aarch64) and hand oracles from the Chrome 159 headless shell
(`body{margin:0;font:16px/1.5 sans-serif}`). Status: all OPEN unless marked
FIXED. The fixes made by the change that filed this record are described in
`doc/00_llm_process/feature_expert/web_render_css_parity/skill.md`
(sections dated 2026-11-14).

Owner file for every layout item:
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_engine.spl`.

## Flex

1. **`flex-direction: column` ignores `flex-grow`.** Container
   `display:flex;flex-direction:column;width:300px;height:90px`, three
   `width:50px` items, the middle one `flex-grow:1`: Chrome middle
   `0,24,50,42`, last `0,66,50,24`; Simple middle `0,24,50,24`, last
   `0,48,50,24`. Matrix ids `cc-fx-fd-col-grow1-t`, `-b`.
2. **`flex-direction: column-reverse` is laid out as a row.** Same container:
   Chrome `a 0,66,50,24`, `t 0,24,50,42`, `b 0,0,50,24`; Simple
   `a 0,0,50,90`, `t 50,0,200,90`, `b 250,0,50,90`. The column branch tests
   `flex_direction == "column"` only. Matrix ids `cc-fx-fd-colrev-*`.
3. **Items of a wrapped flex line are not stretched to the line height.**
   `flex-wrap:wrap`, height 90, two lines: Chrome items are 45 tall
   (`align-content: stretch` splits the free cross space, then
   `align-items: stretch`), Simple 24. Matrix ids `cc-fx-fw-wrap-grow1-*`.
4. **A growing item with an AUTO basis and no width starts from 0.** Text
   items `aa` / `cd` / `bbbb bbbb`, the last two `flex-grow:1` (not `flex:1`),
   in 300 px: Chrome `17.8 / 111.73 / 170.47` (each grows from its content
   width), Simple `18 / 141 / 141`. Only an explicit zero basis is modelled
   exactly; `flex-grow` alone keeps the older weight-share path.
5. **Flex factors are integers.** `flex: 1.5` is rounded to 2 (half up; a
   positive factor below 1 becomes 1): `flex:1.5` beside `flex:1` in 300 px
   gives 200 / 100, Chrome 180 / 120. Pinned as such in
   `flex_grow_definite_size_chrome159_spec.spl` AC-29.
6. **Without a resolved face the flex minimum is a CELL estimate.** The
   longest word is counted in `style_char_w` cells (the unit that lane wraps
   with), so it can differ from the resolved-face minimum by the usual cell
   vs advance error. Measured: `width:100px` + `flex:1` 14-word paragraph in 300 px at 16px/24px gives the right column (100,0,200) but 6 lines (144 px) where Chrome has 3 (72 px) -- the faceless cell wrap, not the minimum.
7. **Min-content of a flex item** takes each text run and child on its own:
   adjacent inline boxes (`ab<b>cd</b>`) are not joined into one word, and a
   replaced child without a `width` counts as its padding and border.
8. **A `flex` basis the parser cannot size is treated as `auto`**
   (`flex: 1 1 50%`, `12rem`, `calc(...)`), never as zero.

## Floats

9. **A FLOAT is fitted at its top row only.** `float_ctx_place_y` asks
   whether the margin box fits beside the floats at one y; a float taller
   than the gap it lands in can overlap a float that starts lower down.
   (Formatting-context BLOCKS are fitted over their whole height.)
10. **A line inside a wrapped run that cannot take its next word stays an
    empty line of one line-height** rather than moving to the exact float
    bottom. The FIRST line of a run does move to the exact bottom.
11. **A formatting-context block with auto height is not re-measured after
    it is narrowed** by a float lower down; if narrowing makes it taller and
    it then meets another float, that float is not avoided.
12. **A generated `::after` clearfix cannot clear**: this renderer builds no
    `::after` box. Block-level `clear` and `<br style="clear:…">` work.
13. **A run that starts mid-line beside a float** (after an inline sibling)
    keeps the mid-line model only when its line is not shortened; otherwise
    it is laid out as one box at the pen.
14. **`td` floats** (`tc-td-fl-*`) are untouched: a `td` whose display is not
    `table-cell` is not laid out (already filed with the matrix).
15. **The collapsed space after an inline float is counted twice**:
    `aa bb <span style="float:left">cd</span> <i>cc</i>` puts `<i>` at 110,
    Chrome 104.48.
16. **An auto-width float takes the wider of two max-content measurements**
    (`flex_item_max_content_width`, `intrinsic_text_width`) because neither
    covers both block children and replaced boxes.
17. **`Style.text_align_set` is set by CSS `text-align` / `text-align-all`
    only.** A presentational `align="left"` attribute is not flagged, so
    under `direction: rtl` it is still treated as the initial value.
18. **`float_ctx_line_boxes` builds a pair for every line down to the lowest
    float** (bounded at 4096 lines) before the run is wrapped, whatever the
    run's length; only the pairs the run used are STORED. A lazy per-line
    query needs the wrap to live beside the float context.

25. **Without a resolved face the float-aware wrap still chops a long word.**
    `compute_style_wrap_ranges_float_band`'s cell-width branch
    (`web_wrap_line_end`) has no whole-word arm, the same as the normal
    faceless wrap (`compute_wrap_ranges`); only the resolved-face branches
    let a word overflow whole.
26. **One twice-layout case remains for a formatting-context block beside
    floats:** when the room over the box's HEIGHT is narrower than at its top
    row, the trial (made at the top-row width) is discarded and the box is
    laid out again at the narrower width. Each such level doubles the work
    below it; the common case (same room over the whole height) reuses the
    trial.
27. **`<td align="left" style="direction:rtl">` is likely still aligned
    `start` (right).** Same cause as item 17: the presentational attribute
    does not set `Style.text_align_set`. Not measured against Chrome.

## Sub / sup

19. **`<sup>` after a WRAPPED text run.** The reopened last line lowers its
    baseline for the sup, but the run's own last line belongs to the tall text
    box placed with line 0 and does not move: words before and after a
    footnote marker can differ by 2-3 px in paint. Element geometry matches.
20. **`vertical-align: sub | super` on inline-block and replaced boxes** keeps
    the flat `font-size / 4` nudge.

## Inline layout, not float-related

21. **A 100 px block wraps `one two three four …` into 9 lines; Chrome 7.**
    `one two three` is 96.95 px wide and fits 100 in Chrome. Fourteen words:
    Simple height 216, Chrome 168.
22. **`<span>bb</span> cc <b>dd</b>` puts `<b>` 6 px right of Chrome** (49 vs
    42.69): the text run between two inline elements is advanced with both of
    its collapsible spaces plus a rounding step.
23. **`line-height: normal` does not override an inherited unitless factor.**
    `body{font:16px/1.5 …}` then `<div style="line-height:normal">`: Chrome
    line 18-21 px, Simple 24.

## Verification gaps

24. **`check-simple-web-engine2d-js-bitmap-evidence.shs` cannot run on a host
    without a self-hosted `bin/simple`**: it refuses the Rust seed
    (`simple_bin_status=forbidden`) and reports `unavailable`. The wiki makes
    that lane a hard bit-exact requirement after every renderer edit, so on
    such a host the requirement is unverifiable rather than met.

## FIXED in the same change (kept for the trail)

- Float-shortened text used the nearest float bottom only; lines now have
  one box each, bounded by all floats intersecting that line.
- Centred / right-aligned / RTL lines beside a float were aligned in the
  full box.
- Zero-basis flex items without a `width` did not add padding and border to
  their share, and had no min-content floor (a `flex:1` label beside an
  over-wide sibling was 1 px wide).
- The float text inset was packed into `first_line_dx` as a negative code and
  the CPU layout execution port read the table raw.
- Second review: a `flex:1` paragraph without a resolved face had a
  paragraph-wide minimum; long words were chopped when the float-aware wrap
  ran on unshortened lines; wrapping flex lines did not redistribute around a
  frozen item; a formatting-context block beside floats was laid out twice
  per nesting level; `direction: rtl` overrode an inherited authored
  `text-align: left`; a nowrap run's minimum was one word; a border-box
  child's width had its padding added again; three `flex:1` items in 400 px
  sat at 0 / 133 / 266.
