# Chrome ↔ pure-Simple web parity — round 10 (2026-09-13, macOS)

Host macOS (Darwin 25.5.0), binary `build/cargo-r2/release/simple`
(`SIMPLE_EXECUTION_MODE=interpreter`), differ
`scripts/check/check-chrome-layout-geometry-diff.shs` at `GEOM_DIFF_HEIGHT=20000`.
One binary and one Chrome per comparison, both sides in this detached worktree:

- **A (before)** — `origin/main` @ `e50d9244965` (round 9's landed tree).
- **B (after)** — A plus the two changes below, and nothing else.

## Round 9's "one wrong ancestor" hypothesis is RETRACTED

Round 9 read `html`'s 135 inherited mismatches as one wrong ancestor box
propagating and predicted a large drop from fixing it. Sorting the 221 root rows
by DOM depth says otherwise. The shallowest rows are `main` (dh 56), `section`
(dh 55) and `ul` (dh 54) — and those are not *causes*, they are the SUM of what
their descendants got wrong: a run of `<li>` rows below them carries `dy` 17,
33, 48, 49 … i.e. an ACCUMULATING offset, not a shared one. An accumulating
offset is by construction not inheritance; each `<li>` is its own root row
because its delta differs from its parent's.

Clustering all three big pages by tag says the same thing with one shape:

| page | `code` root rows | `li`/`p` root rows | everything else |
|---|---|---|---|
| html | 88 | 88 | 45 |
| css-layout | 111 | 159 | 19 |
| css-paint | 151 | 272 | 32 |

`code` (and `kbd`/`samp`) is an inline monospace box, and `li`/`p` are the
blocks that contain them. This is per-line font-metric error ACCUMULATING down
the page, not one bad ancestor.

## The probe that settles it

A 10-line fixture run through the same differ (kept here because it lives in
gitignored `build/`; recreate at `build/probe/mono.html`):

```html
<!doctype html><html><head><meta charset="utf-8"><style>
body{font-family:-apple-system,system-ui,sans-serif;font-size:16px;line-height:24px;margin:8px}
code,kbd,samp,pre{font-family:monospace;font-size:16px}
</style></head><body>
<p><code>x</code></p>
<p><code>abcd</code></p>
<p><code>abcdefg</code></p>
<p><code>MMMMMMMM</code></p>
<p><code>iiiiiiii</code></p>
<p><span>abcdefg</span></p>
<p><span>MMMMMMMM</span></p>
<p><b>abcdefg</b></p>
</body></html>
```

Chrome, at font-size 16 / line-height 24:

| element | Chrome x,y,w,h | Simple before | delta |
|---|---|---|---|
| `<code>abcd</code>` | 8,60,39,19 | h 18 | **h −1** |
| `<span>abcdefg</span>` | 8,224,60,18 | h 18 | h 0 |
| `<p>` holding `<code>` | h 25 | h 24 | **h −1** |
| `<p>` holding `<span>` | h 24 | h 24 | h 0 |

So the monospace inline content area is **19 px, not 18** — and
`inline_content_area_height`'s own comment in
`simple_web_html_layout_renderer_layout.spl` already SAID
"Chrome measures 18 px for the UI sans stack and 19 px for the monospace
`<code>` stack". Only the sans half was ever implemented. Every `<code>`-bearing
line was one pixel short, and the shortfall accumulated: by the bottom of
`html.html` the `<li>` rows sat 49 px above Chrome's.

### Fix 1 — monospace content area

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl:544`
(`style_font_is_monospace` + `inline_content_area_height`): a monospace inline
box is `font_size * 19 / 16`; everything else keeps `9 / 8`. The family
substring list is kept byte-identical to `browser_font_candidates_for_family`
and `_resolved_font_category_uncached` — three lists that disagree is exactly
how the `system-ui` defect below happened.

### What was tried and REVERTED, with its measurement

The same probe shows Chrome's line box holding a `<code>` is 25 px in a 24 px
`line-height` — arithmetically half-leading `(24-19)/2 = 2.5` rounded half up to
3, giving `19 + 2*3`. Implementing that (an inline's contribution to the line
being its line box rather than its content area) is *correct on the probe* and
made `html` **worse: 356 → 428 mismatched**. The real line height is set by the
strut's own ascent/descent, which this layout path does not carry, so the +1 px
lands on lines where Chrome keeps 24. Reverted rather than tuned. **Open debt:
the mono line box is still 1 px short of Chrome's; closing it needs real
per-family ascent/descent in the layout path, not a rounding rule.**

### Fix 2 — `system-ui` resolved to a SERIF face

`src/lib/nogc_sync_mut/text_layout/font_provider.spl:106`. The serif branch
tested `lower.contains("system")`, so a page whose whole stack is `system-ui`
or `-apple-system` measured against Noto Serif. `system-ui` is the UI **sans**
face in every browser; the test moved to the sans branch and the serif branch no
longer claims `system`. Neutral on the catalog (its stacks all contain `sans`),
so it costs nothing in the table below and is a real correctness fix regardless.

This is the live half of round 9's second recorded find. The *latent* half —
`"sans-serif"` matching both `contains("sans")` and `contains("serif")`, safe
only because of the branch order — is now pinned by a spec instead of a comment.
Both finds were already filed at
`doc/08_tracking/bug/web_inline_bold_face_advances_never_selected_2026-09-12.md`
(lines 205-213); no new record was needed.

## Per-page, before → after

`compared` / `mismatched`:

| page | A compared | B compared | A mismatched | B mismatched |
|---|---|---|---|---|
| overview | 18 | 18 | 5 | 5 |
| html | 431 | 431 | 356 | **342** |
| css-layout | 401 | 401 | 384 | 384 |
| css-paint | 528 | 528 | 511 | 511 |
| forms-media | 103 | 103 | 102 | 102 |
| animation | 81 | 81 | 79 | 79 |
| evidence | 4 | 4 | 0 | 0 |
| tab-bar | 9 | 9 | 7 | 7 |
| **total** | **1575** | **1575** | **1444** | **1430** |

Every page other than `html` is byte-identical across A and B, so the −14 is
attributable and nothing regressed. `css-paint` is unmoved: its 455 root rows
cluster into the SAME `code` / `li` / `p` shape as `html`'s, but its remaining
error is advance width (below), which this change does not touch.

## What is actually left, and it is not layout

The same probe measures the remaining error, and every bit of it is font
ADVANCE WIDTH:

| run | Chrome | Simple | note |
|---|---|---|---|
| `<code>MMMMMMMM</code>` | 77 | 74 | mono 9.63 px/char vs 9.25 |
| `<code>iiiiiiii</code>` | 77 | 74 | both fixed-width, so the face is mono |
| `<span>abcdefg</span>` | 60 | 56 | sans, −7% |
| `<span>MMMMMMMM</span>` | 109 | 96 | sans, **−12%** |
| `<b>abcdefg</b>` | 64 | 56 | Chrome bold is +4 over its own regular |

Measured on the LANDED tree, the probe goes 12 → 13 mismatched rows: every
`<code>` **h** now agrees with Chrome (5 rows lose their `dh`), and the
paragraphs holding them re-appear with `dh 1` because the mono LINE box debt
above is unfixed and still accumulates. On a fixture that is nothing BUT mono
paragraphs that accumulation dominates; on the real `html.html` it does not, and
the net there is −14. Both numbers are stated rather than the flattering one.

Under-measured advances are also what produces the `li`/`p` `dh` 16 and 24
clusters on the catalog pages: Simple fits on one line what Chrome wraps to two.
That is a face-metrics problem (the bundled Noto faces are not the faces Chrome
uses), not a layout one, and it is the correct next lane.

## Bold, measured

`<b>abcdefg</b>` is 64 px in Chrome against 60 for the identical regular run —
a real **+4 px** delta from a real bold face. Simple measures **56 for both**,
delta **0**. Round 9's route (`wght=700` instancing of the bundled variable
face via `HVAR`/`gvar`) was NOT implemented this round; items (2) css-paint
clustering and (3) bold instancing were both displaced by the root-cause work
above and the reverted line-box attempt. The bold record stays open.

## Specs

- New: `test/01_unit/browser_engine/monospace_inline_line_box_spec.spl` 5/5;
  sabotaged back to `9/8` for every family, **3 of 5 go RED**.
- New: `test/01_unit/browser_engine/font_family_generic_classification_spec.spl`
  5/5; sabotaged by dropping `system` from the sans branch, **2 of 5 go RED**.
- Neighbours, run in BOTH trees with the same binary, **zero delta**:
  `inline_content_area_half_leading` 4/4, `inline_run_advance_and_break_boxes`
  5/5, `paint_layout_advance_parity` 2/2, `anonymous_block` 4/4,
  `first_child_top_margin_collapse` 10/10, `li_last_child_margin_collapse`
  12/12, `form_control_ua_font` 4/4, `li_nested_list_scope` 5/5,
  `html_tree_builder_flat_projection` 6/6.
- Pre-existing red, NOT touched and identical on both sides: `ifc_linebox_spec`
  is **0/10 at `e50d9244965`** as well. It drives `layout_inline.spl` through
  `layout.{LineBox, layout_inline}` — a separate inline module this change does
  not touch. Fixing it is its own lane.
