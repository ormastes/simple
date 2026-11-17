# html catalog page residual vs Chrome 159 (4.68% at 1x) - classification, 2026-11-17

Status: class 5 (`<a>` without href) FIXED (-139 px, 4.68 -> 4.66); classes 1-4 open, none contained (owners below).
Setup: seed `cargo-target-webrender-blend`, cpu_simd, Chrome 159.0.8154.6, 900x760, tolerance 8 per channel (`pixel_diff.spl`).
Reproduced 32,034 px = 4.68% on base 5dab9c5fcd5. Method as in `web_render_css_paint_residual_2026-11-17.md`:
20-row band histogram of mismatching px, Chrome `getBoundingClientRect` (--dump-dom + inline script) against
`simple_web_layout_debug_layout_by_id`, and a dy credit (a mismatching px that matches when Simple is read one row
up = drift).

## Geometry: Chrome vs Simple (CSS px)

| box | Chrome y,h | Simple y,h |
|-----|-----------|------------|
| h2 | 64.91, 36 | 65, 36 |
| article header (flex, padding 16, h3 margins 18.72) | 120.81, 97.52 | 121, 98 |
| address | 218.33 | 219 |
| figure | 258.33 | 259 |
| dl | 346.33 | 347 |
| p (keyboard) | 458.33 | 459 |
| inventory section | 498.33 | 499 |
| inventory h3 | 538.05 | 539 |

Everything below the `<article><header>` is 0.67 px low in Simple, so every text row and the inner section border
paint one row low (Chrome border row 498, Simple 499; border colours are identical, `199,210,254`). Width and x
match everywhere.

## Partition of the 32,034 mismatching px

| # | class | px | share | owner / contained? |
|---|-------|----|-------|--------------------|
| 1 | Glyph residual in aligned text (LCD mask, hinting, pen phase): below-header remainder after the dy credit and the other classes (19,761) plus h2 and `Article` text (1,757) | ~21,579 | 67.4% | glyph-hint lane and LCD work, not mine |
| 2 | 1-row drift below the header: 7,027 px below y=219 that match with a one-row shift, plus the header's bottom gradient row (810 px, row 218) | 7,837 | 24.5% | not contained (see root cause) |
| 3 | h3 `Feature examples and support` (18.72 px bold): ink 1 row high and wider, `font_size` is `i32` (372 of its 2,771 px are in class 2) | ~2,399 | 7.5% | open, fractional font size (css-paint class 2) |
| 4 | Outer card corners / border AA (x<45, x>=855, y<47) | 80 | 0.25% | tiny, not examined |
| 5 | `<a>` without href drawn as a link (blue `0,0,238`, underline); Chrome draws plain inherited text | 139 | 0.43% | **mine, fixed** |

Rows 1-5 sum to 32,034 (class 1 includes the last image row, 61 px). Overlaps are removed in the order 5, 4, 3, 2, 1, so
class 1 is the remainder and carries the rounding of the others.

## Root cause of class 2 (not fixed)

The first article child is a flex `<header>` (`display:flex; padding:16px 24px`) holding an `<h3>` (UA margins
`1em` = 18.72, line-height 28.08). Chrome: height = 32 + 37.44 + 28.08 = 97.52, so the header ends at 218.33 (starts
at 120.81) and paints rows 121..217. Simple lays the h3 out with whole-pixel margins (19) and height (28), giving
98, and starts the article at the rounded 121, so it ends at 219 and the next block starts a row low. Two known
limits of `block_fractional_margin` combine here, both in the skill doc: a container's own y is rounded before its
children start (children restart `cy_frac` at 0), and flex margins/heights stay whole px. Fixing only the flex height
gives 121 + 97.52 = 218.52, which still rounds to 219 (Chrome 218.33 -> 218), so BOTH are needed: a start fraction
passed into every child layout path and a fractional auto height returned from flex and block containers. That is
a design change across the block, flex, trial-layout and float-band paths (the "two paths measure the same thing
differently" failure), not a contained fix.

## Fix (class 5)

`core.spl` style pass: `tag_defaults` gives every `<a>` the link style, but Chrome's `a:-webkit-any-link` needs an
`href` (an empty `href=""` still counts). The inherited `fg` and underline are restored for an `<a>` whose
`attr_mask` has no `HNODE_ATTR_HREF_BIT`. Chrome 159 computed style: `<a>` and `<a name>` inherit colour and have
`text-decoration-line: none`; `<a href>` and `<a href="">` are `rgb(0,0,238)` + underline. Spec:
`anchor_without_href_chrome159_spec` (4 cases, 2/4 red on base, 4/4 now). Debug fields `color` and `underline` added
to `simple_web_layout_debug_style_by_id` for the pin.

Catalog 1x after: overview 1.29, html 4.66 (31,895 px), css-layout 3.12, css-paint 3.67, forms-media 4.04,
animation 3.59, evidence 0.77, tab-bar 0.42 (only html moved; its baseline row lowered to 4.66).
