# Web ↔ Chrome layout-geometry parity — round 17 (2026-09-14)

Round 17 closes `css-layout` (378 → **5**) and the whole byte/codepoint indexing
residue. It also **disproves the stated cause of its own headline item** — for
the second round running, a premise handed down in the previous record did not
survive contact with a probe.

## Provenance

| | |
|---|---|
| tree | `cf36c7c08cc` (round 16, PR #974) + this change |
| runner | `build/cargo-r2/release/simple`, sha256 `2d0669321ebbc805…` |
| Chrome | `--headless=new --window-size=900,20000` (152.0.7977.83) |
| env | `SIMPLE_EXECUTION_MODE=interpreter`, `SIMPLE_TIMEOUT_SECONDS=0`, `GEOM_DIFF_HEIGHT=20000`, `GEOM_DIFF_TIMEOUT_SECS=1800` |
| command | `sh scripts/check/check-chrome-layout-geometry-diff.shs` |

Three full runs in ONE tree with ONE binary and ONE Chrome. **Run A** was taken
before any edit and reproduces the handed-in baseline exactly (1583 compared,
812 mismatched, per-page identical), so the columns are comparable. **Run B** is
after item 1 alone. **Run C** is after items 1+2.

## The 8-page table

| page | compared | before (A) | after item 1 (B) | after items 1+2 (C) | Δ |
|---|---|---|---|---|---|
| overview | 19 | 5 | 5 | 5 | 0 |
| html | 432 | 230 | 230 | 230 | 0 |
| **css-layout** | 402 | **378** | **5** | **5** | **−373** |
| css-paint | 529 | 9 | 9 | 9 | 0 |
| forms-media | 104 | 103 | 103 | 103 | 0 |
| animation | 82 | 80 | 80 | 80 | 0 |
| evidence | 5 | 0 | 0 | 0 | 0 |
| tab-bar | 10 | 7 | 7 | 7 | 0 |
| **total** | **1583** | **812** | **439** | **439** | **−373** |

Runs B and C are **byte-identical on all eight `*.geometry_diff.md` files**, not
merely equal in count. Item 2 is therefore a correctness fix with zero geometry
effect on this catalog — every catalog element resolves a font, so the flat
fallback helpers it repairs are not on these pages' hot path. That is reported
rather than folded into item 1's number.

## Item 1 — the round-16 cause is false; it was ONE collapsed space

The round-16 record named the dominant `css-layout` cluster as *"a `#text` node
that starts at a non-zero pen x is wrapped independently against the FULL
container width, so an inline sibling before it does not narrow the first line."*

**The pen offset was already applied.** A `print` of the inline formatting path
on the real `css-layout` page, for the `<li>` the record itself cites:

```
R17TEXT|node_w=125|full_adv=125|lines=1|txt=align-content     <- the <code>
R17INL|iw=728|inline_x=125|inline_w=635|avail=603             <- avail = iw - pen
R17TEXT|node_w=603|full_adv=631|lines=2|txt=— partial; values=keyword-nu

R17TEXT|node_w=96|full_adv=96|lines=1|txt=align-self          <- shorter <code>
R17INL|iw=728|inline_x=96|inline_w=635|avail=632
R17TEXT|node_w=632|full_adv=631|lines=1|txt=— partial; values=keyword-nu
```

`avail = iw − inline_x` is right there, and the `align-content` row already
wraps to 2 lines. The two `<li>`s differ only in the `<code>`'s width, and the
whole defect is the last row: **631 against 632**. One pixel of slack, worth a
24 px line box on every such `<li>`.

The missing ~4 px is the **collapsible space** between `</code>` and the text.
CSS 2.1 §16.6.1 collapses a white-space run to one space and removes it only at
the start or end of a LINE; this renderer lays a normal-flow `#text` out from
`text_trimmed = text_data.trim()`, which trims unconditionally, so a run placed
at a non-zero pen lost the space that separates it from its inline sibling.

### The measurement that settles it: let Chrome sabotage the hypothesis

Three `<li>`s, 728 px `<ul>`, 16px/1.5 sans-serif, `<code>` at the UA monospace
default — differing by one character of markup:

| `<li>` content | Chrome | Simple before | Simple after |
|---|---|---|---|
| `<code>align-self</code>` + SPACE + `— partial; …` | 88 | 64 | **88** |
| same, space DELETED from the markup | **64** | 64 | 64 |
| the text alone, i.e. the space at pen 0 | 64 | 64 | 64 |

Row 2 is the discriminator: delete the space and **Chrome itself** drops to 64.
No argument about advance precision, the `<code>` element, or flex sizing
survives that. Row 3 is the control that stops the naive fix — at the start of a
line the space IS dropped, so it must not be charged everywhere.

**Fix** — `simple_web_html_layout_renderer_layout.spl`, in the inline placement
loop immediately before the `avail_inline` clamp: when a `#text` child sits at a
non-zero pen, is not `white-space: nowrap`, and its RAW `text_data` begins with a
collapsible white-space byte, advance the pen by one
`resolved_space_advance(cst, …)` first — so the clamp, the child's x, and the
line-break test all see the true pen. New helper
`text_starts_with_collapsible_space` reads `bytes()[0]`, which is exact: no
UTF-8 continuation byte can equal an ASCII white-space byte.

Spec: `test/01_unit/browser_engine/inline_pen_collapsed_space_spec.spl`, 6/6.
Sabotaged by forcing the pen test false → AC-1 and AC-5 fail, **both controls
(AC-2 space-deleted, AC-3 pen-0) still pass**, which is what proves the spec is
testing the space and not the fixture.

## Item 2 — the byte/codepoint residue was SIX sites, not two

Round 16 named two remaining sites. A census of both layout files and
`…_paint_primitives.spl` for the pattern — a BYTE offset reaching the
CODEPOINT-indexed `char_code_at`/`char_at`, or `txt.len()` used as a loop bound
over them — found six:

| helper | file | old behaviour on non-ASCII |
|---|---|---|
| `text_line_advance_width` | `…_layout` | one flat advance charged per BYTE |
| `wrap_line_end` | `…_layout` | a CHARACTER budget spent in bytes |
| `_lay_ellipsize_text_for_width_inner` | `…_layout` | measured one char, emitted another |
| `_table_text_min_content_width` | `…_layout` | read past the end, over-sized the column |
| `reverse_text_for_paint` | `…_paint_primitives` | counted down from the BYTE length |
| `fb_text_sparse_range`, `fb_text_thin_scaled_clip_range` | `…_paint_primitives` | wrong glyph, advance per byte |

Three of them (`text_line_advance_width`, `_table_text_min_content_width`,
`reverse_text_for_paint`) were never mentioned in round 16 and had been wrong
just as long. **Lesson: when one instance of this mix is found, census the whole
layer in the same pass.**

All six now step by CODEPOINT and test bytes with `bytes()`.
`resolved_text_range_width` is **deleted**, not fixed: the ellipsize loop was its
only caller, and once that loop reads the per-byte advance table the function is
dead — a mixed-index helper left in the tree is a trap for the next reader.

Spec: `test/01_unit/browser_engine/text_byte_codepoint_index_residue_spec.spl`,
9/9, each row with its ASCII twin as a control. Sabotaged by removing the
continuation-byte guard from `text_line_advance_width` → AC-1 and AC-3 fail, all
four ASCII controls still pass. Stated limit: the two framebuffer steppers return
a framebuffer rather than a value and are covered only through the shared
invariant the pure helpers assert.

## Item 3 — the `html` `dy=14` cluster does not exist

Histogrammed `html`'s 85 root mismatches (Run A and Run B agree; item 1 does not
move this page). There is **no `dy=14` cluster**. The distribution is a pure
accumulation ladder — `dy=28` ×17, `dy=56` ×15, `dy=4` ×13 — inherited from a
handful of rows that actually carry a height or width error.

The real cluster, named with the row that identifies it: **a non-replaced
`display:inline` element is given the CONTAINER width, not its content width.**

```
Chrome   path:0/0/4/2/8/1/0 | bdi | x=106 | w=86     (shrink-wrapped to its text)
diff     path:0/0/4/2/8/1/0 | bdi | inline | dx=0 dy=2 dw=642 dh=6
```

Simple reports 728 (the `<li>`'s full content width) where Chrome reports 86.
Ten such root rows on `html` (`bdi`, `bdo`, `cite`, `data`, `del`, `dfn`, …),
each with `dh=6` alongside — the line box (24) charged where the content area
(18) belongs. Not fixed this round: it is outside the brief's four items, and
`inline_w` for non-text inline elements is shared with the `text-align` widening
and the baseline-alignment path, which this round did not read.

## Item 4 — forms-media and animation, histogrammed

Both are single-cluster pages whose root cause is replaced-element intrinsic
sizing, not text layout, so neither is one of items 1-3 and neither was touched.

- **forms-media (103):** `label` ×5, `input` ×3, `option` ×2. First root row
  `path:0/0/1/0 | label | dh=9`, then `path:0/0/1/3 | label | dh=118` (a
  `<textarea>`). Form-control intrinsic heights.
- **animation (80):** `code` ×13, but every one of those is `dx=0 dy=30 dw=0
  dh=0` — a pure inherited ladder. Its origin is two rows above:
  `path:0/0/4 | audio | dx=249 dy=16 dw=510 dh=30` and
  `path:0/0/5 | video | dw=0 dh=126`. `<audio>`/`<video>` default box sizing.

## Neighbours re-run, all unchanged

`non_ascii_run_wrap_byte_advances` 6/6, `paint_layout_advance_parity` 2/2,
`inline_run_advance_and_break_boxes` 5/5, `fractional_advance_accumulation`
6/6, `first_child_top_margin_collapse` 10/10, `li_last_child_margin_collapse`
12/12, `nested_list_container_ua_margin` 8/8.

## What is left

1. `html` 230 — the non-replaced inline element's width (above). Largest
   remaining single cluster on the catalog.
2. `forms-media` 103 — form-control intrinsic heights (`label` `dh=9`).
3. `animation` 80 — `<audio>`/`<video>` default box sizing (`dw=510`, `dh=126`).
4. `tab-bar` 7 — fractional UA font size (filed round 15).
5. `css-paint` 9 / `overview` 5 / `css-layout` 5 — long tails, not yet triaged.
6. Named, not fixed: lines 2+ of a pen-offset run wrap against the REMAINDER
   width rather than the full container width. No page in the catalog measures a
   difference from it (no run there is long enough to expose it), so it is
   recorded rather than guessed at.

## Method notes worth carrying to round 18

- **Verify the handed-down cause against Run A before editing.** Two rounds in a
  row it was wrong. One `print` on the REAL page beat four reduced fixtures.
- **Make the fixture faithful or it will lie.** The first fixture gave `<code>`
  a `sans-serif` family and omitted the `<p>` child; it measured 0 mismatched
  and would have "disproved" a real defect.
- **Sabotage the ORACLE, not just the code.** Changing one character of markup
  and re-measuring Chrome is what converted a plausible story into a proof.
