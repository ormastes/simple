# Web render 1x layout census: html / css-layout / overview (2026-11-19)

Status: census only, no code change. Result: NO layout offsets remain on these three pages.

Method: `check-chrome-catalog-pixel-diff.shs --pages "html css-layout overview"` at 1x (900x760,
Chrome 159, Simple binary `cargo-target-webrender-blend`), pixels with any channel delta > 8
clustered on an 8px grid (8-connected), each cluster padded 2px, then (a) a +-3px shift search of
the Simple box against Chrome, (b) ink bounding box (pixels differing from the Chrome corner
background by > 40) compared on both sides. Ink boxes equal + no shift gain = GLYPH RASTER.

Baselines reproduced: html 1.78, css-layout 2.13, overview 1.13.

Totals: html 12186 mismatching px in 42 clusters (10586 px / 87% in clusters with identical
ink boxes); css-layout 14599 px / 34 clusters (9737 / 67%); overview 7777 px / 21 clusters
(6261 / 81%). No cluster, in any page, improved with ANY shift in +-3px (best shift is 0,0 for
all except two 12px/6px slivers at y=756, which are the 760px frame edge).

## html

| cluster box | element (approx.) | px | class | best shift |
|---|---|---|---|---|
| (45,461)-(500,479) | feature-inventory li text line | 2191 | glyph raster (ink equal) | 0,0 |
| (45,349)-(315,436) | feature-inventory li lines | 1293 | glyph raster (ink equal) | 0,0 |
| (65,543)-(339,563) | li text, `<code>` | 1186 | glyph raster | 0,0 |
| (66,588)-(254,630) | li text | 964 | glyph raster | 0,0 |
| (398,652)-(667,671) | li text (ink bottom 669 vs 668) | 893 | glyph raster (descender/AA, 1px ink edge) | 0,0 |
| (521,588)-(829,605) | li text | 807 | glyph raster | 0,0 |
| (117,71)-(333,92) | section h2 text (ink top 73 vs 74) | 689 | glyph raster (fractional font y) | 0,0 |
| (302,588)-(511,603) | li text | 587 | glyph raster | 0,0 |
| (85,309)-(234,324) | li text | 469 | glyph raster | 0,0 |
| (209,421)-(374,436) | li text | 450 | glyph raster | 0,0 |

## css-layout

| cluster box | element (approx.) | px | class | best shift |
|---|---|---|---|---|
| (474,285)-(856,389) | grid/flex sample text | 1662 | glyph raster (ink equal) | 0,0 |
| (105,530)-(488,573) | sample block text (ink bottom 571 vs 570) | 1607 | glyph raster | 0,0 (shift worsens) |
| (105,634)-(477,677) | sample block text (475 vs 474) | 1566 | glyph raster | 0,0 |
| (65,422)-(339,442) | li text | 1186 | glyph raster | 0,0 |
| (521,466)-(829,483) | li text | 807 | glyph raster | 0,0 |
| (106,698)-(417,716) | text | 790 | glyph raster | 0,0 |
| (106,594)-(417,612) | text | 790 | glyph raster | 0,0 |
| (43,290)-(427,389) | text | 653 | glyph raster | 0,0 |
| (302,466)-(511,481) | li text | 587 | glyph raster | 0,0 |
| (767,225)-(846,260) | text | 577 | glyph raster | 0,0 |

Heading clusters (47,71) (214,71) (350,71) have ink top 73 vs 74: the same fractional-font
y-raster as `web_render_forms_media_fractional_font_y_raster_2026-11-19.md`.

## overview

| cluster box | element (approx.) | px | class | best shift |
|---|---|---|---|---|
| (212,291)-(342,330) | text | 1500 | glyph raster (ink equal) | 0,0 |
| (85,235)-(488,250) | text line | 1219 | glyph raster | 0,0 |
| (359,195)-(610,213) | text (ink right 607 vs 608) | 861 | glyph raster | 0,0 |
| (127,195)-(289,213) | text | 724 | glyph raster | 0,0 |
| (42,142)-(266,163) | heading (ink top 144 vs 145) | 655 | glyph raster (fractional y) | 0,0 |
| (65,291)-(179,330) | text | 633 | glyph raster | 0,0 |
| (44,77)-(183,102) | text | 495 | glyph raster | 0,0 |
| (354,77)-(422,102) | text | 365 | glyph raster | 0,0 |
| (537,82)-(608,109) | text | 330 | glyph raster | 0,0 |
| (443,82)-(525,102) | text | 260 | glyph raster | 0,0 |

Element names are positional approximations (the catalog pages are dense text); the class
verdict does not depend on them.

## Root cause / conclusion

No LAYOUT OFFSET and no OTHER (colour, border, gradient) cluster exists among the 97 clusters.
The only geometric deviations are 1px ink-edge differences at heading text (top row 73/144 vs
74/145) and a few descender rows, all of which are the known fractional-font y-raster / AA
items. Remaining work on these three pages is glyph rasterization (y-scaling of fractional
font sizes, coverage), not layout; further layout hunting here has no expected yield.
