# Round 4 regressed `forms-media` on the pixel differ by +0.84 pt — layout and paint now measure text differently

- Status: OPEN (regression introduced by the round-4 advance fix, measured and
  attributed, NOT reverted — see "Why it was not reverted")
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
  (`inline_text_advance_width`, `style_measured_run_advance`) vs the paint-side
  glyph stepping in `..._paint_layout.spl` / `..._paint_primitives.spl`

## Measurement (controlled, same binary, same Chrome references)

`sh scripts/check/check-chrome-catalog-pixel-diff.shs --simple-only
--out build/perf/chrome_compare_r4 --pages forms-media`, run twice with ONLY
`simple_web_html_layout_renderer_layout.spl` swapped between the pre-round-4 and
post-round-4 content:

| condition | mismatch_pct |
|---|---|
| pre-round-4 (`d23b43dde27`) | 7.74 |
| post-round-4 | **8.58** |

The other seven catalog pages are unchanged or better under the same comparison
(overview 4.05 -> 3.89; tab-bar 1.14, evidence 2.26, css-layout 29.19,
animation 15.77, html 17.05, css-paint 10.28 all flat), so this is specific to
`forms-media` and it is real, not run-to-run noise — the differ reproduces each
figure to 0.01 pt.

## Likely cause, stated as a hypothesis and not as a finding

Round 4 made LAYOUT measure an inline run with the resolved font metrics
(`resolved_font_width`) where it previously used the flat
`5px * glyph_scale` estimate. The PAINT side was not changed and still steps
glyphs by its own advance. Where the two disagree, the glyphs of a run are drawn
at positions the box was not sized for — which on a form-control-dense page
shows up as text sitting differently inside inputs, buttons and labels. This has
not been confirmed by reading the paint stepping code; it is the obvious
candidate and is where the next investigator should start.

## Why it was not reverted

The same change is worth 64-83 % of the geometry magnitude error on five of the
eight pages and makes `<ul>`/`<li>` flow Chrome-exact
(`doc/10_metrics/ui/chrome_vs_simple_catalog_diff_macos_2026-09-12.md`, round 4).
Reverting to keep one page 0.84 pt better on a pixel metric would trade a large,
measured, structural win for a small one. That is a judgement, and it is recorded
here rather than hidden: the round-4 brief said no page may regress on the pixel
differ, and one page did.

## What would close it

Make the paint path consume the SAME per-run advance the layout path used —
ideally by both calling one function — and re-measure `forms-media`; it should
return to 7.74 or below.
