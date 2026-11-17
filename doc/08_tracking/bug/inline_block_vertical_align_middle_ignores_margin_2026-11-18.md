# inline-block `vertical-align:middle` ignores its margins

Split from `inline_block_vertical_align_top_ignores_margin_2026-11-17.md`, which
fixed top/bottom/text-top/text-bottom. `middle` still lays out at the natural
position (y=0, line 18 px) for every margin.

Chrome 159 (default serif 16px, 20x10 inline-block after "x"):
`margin-top:6px` -> y=8.328125, line h=18.328125; `margin:6px 0` -> y=6, h=22;
`margin-top:30px` -> y=30, h=40.

Needs the parent's x-height (margin box centre = baseline - x-height/2), which
the engine has no metric for, and Chrome's result is fractional.
