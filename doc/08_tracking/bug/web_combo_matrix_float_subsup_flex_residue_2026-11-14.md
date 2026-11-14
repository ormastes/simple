# Web renderer: residue found while fixing floats, sub/sup and flex-grow

Found 2026-11-14 with the combination matrix
(`sh scripts/check/check-web-combo-matrix-chrome.shs`, Chrome 159.0.8154.6,
Linux aarch64) and hand oracles from the Chrome 159 headless shell
(`body{margin:0;font:16px/1.5 sans-serif}`, 900x2000). Status: all OPEN.
None of these is fixed by the change that filed this record; the fixes that
change did make are in
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
4. **A growing item with an AUTO width and an AUTO basis starts from 0.**
   Text items `aa` / `cd` / `bbbb bbbb`, the last two `flex-grow:1`, in 300
   px: Chrome `17.8 / 111.73 / 170.47` (each grows from its content width),
   Simple `18 / 141 / 141`. The nowrap row pass shares the remainder by weight
   from a zero base for every auto-width growing item.
5. **Zero-basis items without a `width` do not add padding and border to
   their share.** They keep the pre-existing weight-share path, which hands
   out OUTER widths. (With a `width` the zero-basis path is exact; see the
   flex spec.)
6. **A zero-basis item is not floored at its min-content width while it
   grows**, and in a wrapping container a `flex:0` item is measured at its
   padding and border only.

## Floats

7. **A float is fitted at its top row only.** `float_ctx_place_y` asks whether
   the margin box fits beside the floats at one y; a float taller than the gap
   it lands in can overlap a float that starts lower down.
8. **Lines beside a float are wrapped by a line COUNT, not per line.** The run
   gets `ceil((float bottom - y) / line-height)` narrow lines at the width
   measured on its first line. Two floats of different heights on one side, or
   a taller line, wrap at the wrong width from the second step on.
9. **Text that is centred, right-aligned or RTL beside a float** whose lines
   outlast the float is aligned in the full box on the narrow lines.
10. **A run that starts mid-line beside a float** keeps the mid-line model
    only when the line is not shortened; otherwise it is laid out as one box.
11. **`td` floats** (`tc-td-fl-*`) are untouched: a `td` whose display is not
    `table-cell` is not laid out (already filed with the matrix).
12. **The collapsed space after an inline float is counted twice**:
    `aa bb <span style="float:left">cd</span> <i>cc</i>` puts `<i>` at 110,
    Chrome 104.48.

## Sub / sup

13. **`<sup>` after a WRAPPED text run.** The reopened last line lowers its
    baseline for the sup, but the run's own last line belongs to the tall text
    box placed with line 0 and does not move: words before and after a
    footnote marker can differ by 2-3 px in paint. Element geometry matches.
14. **`vertical-align: sub | super` on inline-block and replaced boxes** keeps
    the flat `font-size / 4` nudge.

## Inline layout, not float-related

15. **A 100 px block wraps `one two three four …` into 9 lines; Chrome 7.**
    `one two three` is 96.95 px wide and fits 100 in Chrome. Fourteen words:
    Simple height 216, Chrome 168.
16. **`<span>bb</span> cc <b>dd</b>` puts `<b>` 6 px right of Chrome** (49 vs
    42.69): the text run between two inline elements is advanced with both of
    its collapsible spaces plus a rounding step.
17. **`line-height: normal` does not override an inherited unitless factor.**
    `body{font:16px/1.5 …}` then `<div style="line-height:normal">`: Chrome
    line 18-21 px, Simple 24.

## Verification gaps

18. **`check-simple-web-engine2d-js-bitmap-evidence.shs` cannot run on a host
    without a self-hosted `bin/simple`**: it refuses the Rust seed
    (`simple_bin_status=forbidden`) and reports `unavailable`. The wiki makes
    that lane a hard bit-exact requirement after every renderer edit, so on
    such a host the requirement is unverifiable rather than met.
