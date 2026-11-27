# inline-block `vertical-align:middle` ignores its margins

Split from `inline_block_vertical_align_top_ignores_margin_2026-11-17.md`, which
fixed top/bottom/text-top/text-bottom. `middle` still lays out at the natural
position (y=0, line 18 px) for every margin.

Chrome 159 (default serif 16px, 20x10 inline-block after "x"):
`margin-top:6px` -> y=8.328125, line h=18.328125; `margin:6px 0` -> y=6, h=22;
`margin-top:30px` -> y=30, h=40.

Needs the parent's x-height (margin box centre = baseline - x-height/2), which
the engine has no metric for, and Chrome's result is fractional.

## Resolved 2026-11-18

The x-height now comes from the face's OS/2 `sxHeight`
(`browser_face_x_height_units`), and `align_inline_line_baselines` places a
`middle` atomic by its margin box in 1/64 px, snapping the top half up. The
`margin-top:6px` and `margin-top:30px` cases above now give y=8, h=18 and y=30,
h=40 (Chrome rounded half up). Pinned by
`test/01_unit/browser_engine/vertical_align_middle_margin_chrome159_spec.spl`.
Still open: device scale > 1 keeps boxes CSS-snapped (2-3 device px off Chrome
at dpr4), and `middle` on a plain inline element.
