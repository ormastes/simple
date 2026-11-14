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
6. **Wrapping flex lines: an item frozen at its minimum does not hand its
   unused share to its line-mates.** The nowrap path redistributes (AC-25);
   the wrap path clamps the item and leaves the others at their first share,
   so a line can overflow by the clamped amount.
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
17. **RTL default alignment is a heuristic.** `direction: rtl` switches an
    undeclared `text-align` to `start`; an INHERITED authored
    `text-align: left` is indistinguishable from the default and is switched
    too.

## Sub / sup

18. **`<sup>` after a WRAPPED text run.** The reopened last line lowers its
    baseline for the sup, but the run's own last line belongs to the tall text
    box placed with line 0 and does not move: words before and after a
    footnote marker can differ by 2-3 px in paint. Element geometry matches.
19. **`vertical-align: sub | super` on inline-block and replaced boxes** keeps
    the flat `font-size / 4` nudge.

## Inline layout, not float-related

20. **A 100 px block wraps `one two three four …` into 9 lines; Chrome 7.**
    `one two three` is 96.95 px wide and fits 100 in Chrome. Fourteen words:
    Simple height 216, Chrome 168.
21. **`<span>bb</span> cc <b>dd</b>` puts `<b>` 6 px right of Chrome** (49 vs
    42.69): the text run between two inline elements is advanced with both of
    its collapsible spaces plus a rounding step.
22. **`line-height: normal` does not override an inherited unitless factor.**
    `body{font:16px/1.5 …}` then `<div style="line-height:normal">`: Chrome
    line 18-21 px, Simple 24.

## Verification gaps

23. **`check-simple-web-engine2d-js-bitmap-evidence.shs` cannot run on a host
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
