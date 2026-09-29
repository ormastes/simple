# Vertical block flow drifts ~16 px per occurrence of one construct (2026-09-14)

Status: **FIXED 2026-09-14 (round 15)**. Characterised in round 14 (below,
retained unchanged); root-caused and fixed in round 15. Measured on one tree,
one binary and one Chrome harvest, toggling only the fix:
`html` 330 → **230** mismatched, every other catalog page byte-identical.

## Round 15: what it actually was — and what it was NOT

**The round-14 hypothesis in "Where the first step happens" below is WRONG and
was ruled out by measurement, not by argument.** The anonymous block box CSS
2.1 §9.2.1.1 requires around an inline run with a block sibling is implemented
correctly and always was. Fixtures that prove it (`test/fixtures/browser/
anon_block_box.html`, `anon_block_box2.html`, `anon_v0..v3.html`, each diffed
against Chrome through `check-chrome-layout-geometry-diff.shs`):

| fixture | Chrome | Simple | verdict |
|---|---|---|---|
| `<li><code/><div/></li>`            | div at li+18 | li+18 | MATCH |
| `<li>text<div/></li>`               | div at li+18 | li+18 | MATCH |
| `<div><span/><div/></div>`          | div at +18    | +18   | MATCH |
| `<div><span/><ul>..</ul></div>`     | ul at +18+16  | same  | MATCH |
| `<li><code/><p/></li>`              | p at li+18+16 | same  | MATCH |
| `<li><code/><ul>..</ul></li>`       | ul at li+18   | li+35 | **16 px too low** |
| `<li><code/><dl><dt/></dl></li>`    | dl at li+18   | li+35 | **16 px too low** |

The line box is right in every row. Only a **list container** nested in a list
is wrong, and it is wrong by exactly its own UA `margin-block-start`.

### Root cause 1 — a missing UA rule

Chrome's `html.css` carries a descendant block zeroing the block margins of
`dir`/`dl`/`menu`/`ol`/`ul` that have a `dir`/`dl`/`menu`/`ol`/`ul` ANCESTOR
(`ul ul, ul ol, ul dl, ol ul, dl dl, menu ul, …` — the full 5×5 cross product).
Simple had no such rule, so every nested list carried a 16 px top margin Chrome
does not give it, and 16 px of it also reappeared at the bottom.

Verified against Chrome's own computed values rather than assumed: the `dl` in
`<ul><li><code/><dl/></li></ul>` reports `margin-top=0px` in
`getComputedStyle`, while the `ul` in `<div><span/><ul/></div>` reports 16 px.

**Why it hid for so long, and why the drift looked like an anonymous-block
bug:** when the nested list is the li's FIRST in-flow child its 16 px top margin
collapses through the li anyway (see
`first_child_top_margin_collapse_spec.spl`), so the geometry came out right for
the wrong reason. An inline run before it removes that cover — and that is
exactly the `<li><code>…</code><ul>…</ul></li>` shape all over `html.html`,
which is why the first step landed at an inline→block boundary and pointed
every investigation at the anonymous box.

Fix: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl`
— `list_container_tag()` / `has_list_container_ancestor()` (defined just above
`compute_styles`), applied immediately after `tag_defaults(st, nd.tag)`, which
is where the ancestor chain is known and still ahead of every author
declaration, as a UA rule must be.

### Root cause 2 — the style-cascade memo key omitted the new input

With only fix 1, `ol`-in-`ul` and `dl`-in-`ul` went green while **`ul` inside
`ul` stayed broken** — the one nesting the catalog page actually uses. The
cascade memo (same file, `memo_key`) is keyed on
`(parent inherit id, tag, em_base, writing mode, pres_decls, combined_decls)`
and its comment asserts `st` is a deterministic function of those. The new UA
bit reads the ANCESTOR chain, so two `<ul>`s with the same tag and the same
inherit-identity parent can legitimately disagree about it: the nested `<ul>`
hit the outer `<ul>`'s cached entry and copied the 16 px margin straight back
over the zeroing. `{nested_list_ua}` is now part of the key.

The memo is only active when `combined_decls != ""`, i.e. when some author rule
matches — which is why a bare-UA fixture cannot expose root cause 2. The spec's
fixture head carries `*{box-sizing:border-box}` for exactly that reason; do not
"simplify" it away.

### Spec

`test/01_unit/browser_engine/nested_list_container_ua_margin_spec.spl`, 8/8.
Five assertions on the rule (ul-in-ul, dl-in-ul, ul-in-ol, non-parent ancestor,
the zeroed bottom margin) and three CONTROLS that must keep their 16 px (a
`<ul>` with no list ancestor, and a `<p>` inside a list). Both halves are
sabotage-proven independently: disabling the UA rule reds AC-1..5; removing
only `{nested_list_ua}` from the memo key reds exactly AC-1/2/5 and leaves
AC-3/4 green, which is the signature that would otherwise make a later key
"simplification" look harmless.

### Still open, surfaced by the same fixtures and deliberately not fixed here

- **An outer `<ul>`'s top margin does not collapse out of `<body>`.** Chrome
  puts `<ul>` at y=0 under `body{margin:0}`; Simple puts it at 16. Visible as
  `body dy=8` on `anon_block_box.html` and as the reason every absolute-y
  assertion in the new spec neutralises the outer list with
  `style="margin:0;padding:0"`.
- **The `dy=14` rows below** (vs 17) still suggest a second line-height in play
  on `html`. Round 15 did not chase it.
- The remaining `css-layout` / `css-paint` / `forms-media` / `animation`
  block-flow clusters are a DIFFERENT cause: those pages contain no nested
  lists and their numbers did not move at all under this fix.

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
