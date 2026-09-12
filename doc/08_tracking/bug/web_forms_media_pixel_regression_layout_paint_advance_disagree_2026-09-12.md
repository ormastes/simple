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

## Round 5 (2026-09-12) — CLOSED as filed; the mechanism was found, and it was not where this record guessed

Status: the layout/paint disagreement is fixed. The `<= 7.74` acceptance figure
in the round-4 brief could NOT be tested, for a reason this record could not have
known: at `origin/main` @ `43cb44149fe`, **`forms-media` rendered zero pixels**,
along with four other catalog pages
(`doc/08_tracking/bug/web_drawir_advances_staged_per_byte_kills_render_2026-09-12.md`).
There was no comparable "before" on that tree at all.

**Where the disagreement actually was.** This record's hypothesis — "paint still
steps glyphs by its own advance" — was right in spirit and wrong in location. The
catalog does not render through the CPU framebuffer painter at all; it goes
through Draw-IR into Engine2D. On that path the divergence was specific: a
**wrapped** text run was emitted with `draw_ir_text_styled_clipped`, carrying no
advances, while layout had sized each of its lines from the resolved metrics. The
code said so itself — "A wrapped node always uses the fixed-advance measurement
model ... noted here as a scope simplification". Form-control-dense pages are
exactly where wrapped labels dominate, which is why this page and not the others.

`_html_draw_ir_resolved_text_command` is now shared by the single-line,
first-wrapped-line and extra-wrapped-line emitters, so all three measure a run
the way layout did. The CPU framebuffer path was ALSO unified onto one per-byte
advance table (`style_run_byte_advances`), which is what this record described;
that half is real but is not what moved this page's number.

**Measured, same binary, same Chrome references:** `forms-media` 0 px
(unreadable) -> **8.11**. Round 4 recorded 8.58 on a tree where the page still
rendered, and 7.74 pre-round-4. Against the only baseline that exists on this
tree, the page went from no output to 8.11 and no other page regressed; against
round 4's context figure it improved by 0.47. Whether the residual 0.37 above
7.74 is the same defect cannot be answered from these runs, so it is not claimed
either way.

Pinned by `test/01_unit/browser_engine/paint_layout_advance_parity_spec.spl`
(`2 examples, 0 failures`) with a three-way sabotage, and by the round-5 table in
`doc/10_metrics/ui/chrome_vs_simple_catalog_diff_macos_2026-09-12.md`.
