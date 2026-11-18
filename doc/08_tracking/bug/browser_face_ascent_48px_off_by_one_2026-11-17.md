# browser_face_ascent_descent_px ascent is 1px low at 48px (serif, sans-serif)

Found by the coverage lane, 2026-11-17.

## Symptom
Baseline (ascent) at font-size 48px, `line-height: normal`:

| family | Chrome 159 | Simple |
|---|---|---|
| serif | 44 | 43 (descent 10) |
| sans-serif | 44 | 43 (descent 10) |
| monospace | 45 | 45 (matches) |

Sizes 12, 16, 24, 32 match Chrome for all three families, and normal line
height matches at all 15 size/family points (so the line box is right; the
split between ascent and descent is what is off).

## Repro
Chrome: a `position:absolute` div, `font-family:serif; font-size:48px;
line-height:normal`, text `Hxg` followed by `<span style="display:inline-block;width:1px;height:0">`;
the span's `getBoundingClientRect().bottom` is the baseline = 44
(`chrome --headless --no-sandbox --dump-dom`, chromium-1255).
Simple: `browser_face_ascent_descent_px("serif", false, false, 48)` returns `[43, 10]`
(`src/lib/nogc_sync_mut/text_layout/font_renderer.spl:3499`); same for `"sans-serif"`.
Spec with the Chrome-measured rows:
`test/01_unit/browser_engine/browser_face_line_metrics_chrome159_spec.spl`
(the two 48px ascent assertions are deliberately omitted until fixed).

## Suspected cause
`sfnt_line_metric_units_ascent_descent_px` (called at font_renderer.spl:3515)
rounds ascent and descent independently. Chrome rounds ascent, then derives
descent so ascent+descent equals the rounded line height or rounds the
unrounded ascent differently (Skia `SkScalarRoundToScalar(-ascent)`). At 48px
ascent*scale lands near a .5 boundary for the Liberation faces, so a
round-half difference gives 43 vs 44. Not verified in code; confirm by printing
the unrounded ascent units*48/unitsPerEm for Liberation Serif/Sans.

## Acceptance
Add `_check("serif", 48, 55, 44)` and `_check("sans-serif", 48, 55, 44)` to the
spec above, green, with the 12-32px and monospace rows unchanged.

## Resolution (2026-11-18): not an engine bug
Liberation Serif/Sans hhea 1825/434-443/67-87 per 2048 em at 48px: ascent 42.77 -> 43,
descent 10.2-10.4 -> 10, line gap 2 (rounded). Chrome's 44 is the BASELINE: rounded ascent
43 + floor(gap 2 / 2) = 1. `browser_face_ascent_descent_px` correctly returns 43; the strut
(`inline_line_strut_baseline_offset`) already yields baseline 44 and line height 55 (marker
y 34 + h 10). The record conflated face ascent with line baseline. Pinned by
`test/01_unit/browser_engine/line_strut_baseline_large_chrome159_spec.spl` (48/64/72px, all three
families, Chrome-measured, green on base with no source change).
