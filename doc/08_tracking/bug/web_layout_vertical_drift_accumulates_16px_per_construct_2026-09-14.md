# Vertical block flow drifts ~16 px per occurrence of one construct (2026-09-14)

Status: **OPEN** — characterised with evidence, not yet fixed. Round 14, next
root cause after the render-budget truncation
(`web_render_budget_truncates_geometry_differ_layout_2026-09-14.md`).

## What the histogram says

First honest html diff (431 compared, 329 mismatched: root 136, inherited 193).
Across the **136 root mismatches**, `|delta|` distributes like this:

| component | zero | non-zero |
|---|---|---|
| dx | **135** | 1 |
| dw | **119** | 17 |
| dh | **103** | 33 |
| dy | **0** | **136** |

Horizontal geometry is essentially correct. **Every single root mismatch is a
vertical-position error**, and the widths and heights of the boxes themselves
mostly are not. So this is not a viewport width, root font-size, UA margin, or
differ-origin problem — all four of those would move dx or scale dw.

## It is an accumulation, not a scale

`dy` is not proportional to Chrome's `y` (the ratio `dy/y` *falls* from 6‰ to
0‰ down the page). It is flat across runs of consecutive elements and then
**steps by ~16 px**:

```
chrome_y   dy
2510        2
2587        1
2611       17     <- first step
2675       17
2715       17
2742       14
3131       33     <- 2 x 16
3259       49     <- 3 x 16
3896       49
```

`dy = chrome_y - simple_y > 0`, i.e. the Simple document is **shorter** than
Chrome's: each occurrence of some construct contributes ~16 px too little
height, and the deficit accumulates down the block flow. Every later element is
then displaced by the running total — which is exactly why 193 of the 329
mismatches classify as *inherited*.

## Where the first step happens

Chrome's rows bracketing the first step:

```
2587  path:0/0/4/2/19     li    728x112
2589  path:0/0/4/2/19/0   code   19x19
2611  path:0/0/4/2/19/1   div   728x48
2611  path:0/0/4/2/19/1/0 dl    728x48
2611  ...             /0/0 dt    728x24
2635  ...             /0/1 dd    688x24
```

The `li` at 2587 is still nearly correct (`dy=1`); the `div` at 2611 and
everything inside it is already 17 px off. The 16 px is therefore lost **inside
the `li`, between the inline `<code>` run and the block `<div>` that follows
it** — i.e. in the **anonymous block box** CSS requires around an inline run
that has a block sibling. Chrome gives that anonymous block a full line box
(2587..2611 = 24 px, the 16 px font's default line-height); the Simple side
appears to give it far less. The `dy=14` rows (vs 17) suggest more than one
line-height in play rather than a single constant.

## Next step for whoever picks this up

Build a minimal fixture — `<li><code>x</code><div>y</div></li>` — and compare
the anonymous-block height against Chrome through the same differ
(`GEOM_DIFF_PAGES=<path-to-fixture>` accepts a path). Confirm before touching
the cascade: the 16 px could equally be a missing default vertical margin on
one of `dl`/`p`/`div` in the UA stylesheet, which the same fixture separates.
Do **not** infer the fix from the aggregate table; the accumulation makes every
downstream row look like independent evidence for whatever hypothesis is held.
