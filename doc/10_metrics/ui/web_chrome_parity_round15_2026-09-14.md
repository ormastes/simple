# Web ↔ Chrome layout-geometry parity — round 15 (2026-09-14)

Round 14 left one open root cause (a ~16 px vertical deficit accumulating once
per construct) and one open cluster (`tab-bar` flex-item widths). Round 15
closes the first and disproves the stated diagnosis of the second.

## Provenance

| | |
|---|---|
| tree | `e5876d9a957` (round 14, PR #967) + this change |
| runner | `build/cargo-r2/release/simple`, sha256 `2d0669321ebbc805…` |
| Chrome | `--headless=new`, `--window-size=900,20000` |
| env | `SIMPLE_EXECUTION_MODE=interpreter`, `SIMPLE_TIMEOUT_SECONDS=0`, `GEOM_DIFF_HEIGHT=20000`, `GEOM_DIFF_TIMEOUT_SECS=1800` (the harness pins `SIMPLE_WEB_RENDER_BUDGET_MS` itself) |
| command | `sh scripts/check/check-chrome-layout-geometry-diff.shs` |

**Both rows of the table below were measured in ONE tree with ONE binary and
ONE Chrome, toggling only the fix** — the "before" run reverted exactly the two
edits and nothing else. It is not a comparison against round 14's numbers, which
were taken before the `<body>` harvest fix and therefore have a different
`compared` count.

## The 8-page table, before and after

| page | compared | mismatched before | mismatched after | Δ |
|---|---|---|---|---|
| overview | 19 | 5 | 5 | 0 |
| **html** | 432 | **330** | **230** | **−100** |
| css-layout | 402 | 337 | 337 | 0 |
| css-paint | 529 | 516 | 516 | 0 |
| forms-media | 104 | 103 | 103 | 0 |
| animation | 82 | 80 | 80 | 0 |
| evidence | 5 | 0 | 0 | 0 |
| tab-bar | 10 | 7 | 7 | 0 |
| **total** | **1583** | **1378** | **1278** | **−100** |

`html` root mismatches fall 136 → 84 and inherited 193 → 146. Seven of eight
pages are byte-identical across the toggle, which is the evidence that this is
a targeted fix and not a global nudge: the other pages contain no nested lists.

## Root cause: a missing UA rule, and a memo key that hid half of it

Not the anonymous block box. Round 14's hypothesis — that the CSS 2.1 §9.2.1.1
anonymous block around an inline run with a block sibling was dropping its line
box — **was ruled out by measurement**: fixtures with `div`, bare text, `span`
and `p` in that exact position all match Chrome to the pixel. Only a *list
container nested in a list* was wrong, by exactly its own UA margin.

1. **Missing UA rule.** Chrome's `html.css` zeroes the block margins of
   `dir`/`dl`/`menu`/`ol`/`ul` with a list-container ANCESTOR (the 5×5
   descendant cross product). Simple had no such rule. It hid because such a
   list is usually the li's first child, where the margin collapses through the
   li anyway — an inline run before it removes that cover, which is why the
   first observed step was at an inline→block boundary.
2. **Cascade memo key.** With only (1), `ul`-in-`ul` — the nesting the page
   actually uses — stayed broken: the memo is keyed on
   `(parent inherit id, tag, em_base, writing mode, pres_decls, combined_decls)`
   and the new bit is ancestor-derived, so the nested `<ul>` copied the outer
   `<ul>`'s cached 16 px back over the zeroing.

Fix: `simple_web_html_layout_renderer_core.spl` (`list_container_tag`,
`has_list_container_ancestor`, applied after `tag_defaults`; `{nested_list_ua}`
added to `memo_key`). Full record, including the ruled-out hypothesis and the
fixture table:
`doc/08_tracking/bug/web_layout_vertical_drift_accumulates_16px_per_construct_2026-09-14.md`.

Spec: `test/01_unit/browser_engine/nested_list_container_ua_margin_spec.spl`,
8/8, with three controls that must KEEP their 16 px, and each of the two
defects sabotage-proven separately.

Neighbours re-run, unchanged: `li_last_child_margin_collapse` 12/12,
`first_child_top_margin_collapse` 10/10, `inline_run_advance_and_break_boxes`
5/5, `paint_layout_advance_parity` 2/2, `ifc_linebox` 0/10 (pre-existing, not
touched).

## tab-bar: not a flex formula

Round 14 listed `tab-bar`'s 7/7 `flex-item` width cluster as a candidate
single-formula fix. It is not. The buttons are content-sized with no
`flex-basis`/`flex-grow` override, and the errors are a flat 1-2 px per item
regardless of item width (74 px and 108 px are both off by 2) with `dx` the
running sum. Chrome computes their font size as **`13.3333px`**; Simple's
`Style.font_size` is `i32`, so the fractional UA form-control size is lost and
every label measures short. Changing the constant would trade this page's error
for every other page's, so it is filed rather than patched:
`doc/08_tracking/bug/web_tab_bar_flex_item_widths_fractional_font_size_2026-09-14.md`.

## What is left

1. `css-layout` / `css-paint` / `forms-media` / `animation` block-flow clusters
   — a different cause, untouched by this fix (zero movement).
2. An outer `<ul>`'s top margin does not collapse out of `<body>` (Chrome y=0,
   Simple y=16). Surfaced by the round-15 fixtures; recorded in the bug file.
3. The `dy=14` rows on `html` still suggest a second line-height.
4. `tab-bar` sub-pixel font size (filed above) — a style-model question, not a
   layout one.

## Incidental: seed lint cannot lint these spec files

`simple lint` on the new spec dies with `semantic: string index out of bounds:
index is 5692 but length is 5692`, pointing at the leading `"""` docstring. The
**same crash reproduces on the already-landed
`first_child_top_margin_collapse_spec.spl`** (index 5690, length 5690), so it is
a pre-existing seed defect on docstring-leading spec files, not introduced here.
The touched library file lints clean (0 errors, 65 pre-existing warnings, none
in the changed region).
