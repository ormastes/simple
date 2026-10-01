# Chrome ↔ pure-Simple web parity — round 8 (2026-09-13, macOS)

Host: macOS (Darwin 25.5.0), worktree
`.claude/worktrees/agent-aa83f642a1d856b17`, binary
`build/cargo-r2/release/simple` (`SIMPLE_EXECUTION_MODE=interpreter`).
Geometry differ `scripts/check/check-chrome-layout-geometry-diff.shs` at
`GEOM_DIFF_HEIGHT=20000`. Both sides measured in THIS worktree with THIS binary
(`.claude/rules/testing.md` § Measurement traps): BEFORE is the tree at
`origin/main` + the M14-only commit; AFTER adds the renderer-lane change, and
nothing else differs.

**The pixel differ was again not usable on this host.** Round 7 recorded Chrome
hitting the 90 s `--screenshot` alarm on every catalog page; round 8 did not
spend budget re-confirming it and relied on the geometry differ + specs, as the
brief permits.

## (1) TABLES — `table_layout_spec` 0/7 → 9/9

### Root cause

The spec-facing M14 layout API exported `layout_block` but **no `layout_table`
at all** — `test/01_unit/browser_engine/table_layout_spec.spl:4` imports it from
`std.gc_async_mut.gpu.browser_engine.layout`, and the symbol did not exist, so
all 7 examples failed at load. `layout_table.spl` held only DOM-traversal
helpers (row/cell collection, colspan parsing) plus a
`_compute_col_widths` that splits the width EVENLY — i.e. the fixed-layout rule,
not CSS 2.1 §17.5.2.2 automatic layout.

Separately, in the Draw-IR renderer lane,
`explicit_auto_table_column_offsets`
(`simple_web_html_layout_renderer_layout.spl:1152`) **bailed out of automatic
layout entirely** (`return []`) for any table whose cells state no `width`,
which is nearly every real table. Those tables fell through to the equal-split
fill path. Auto cells that did reach the sizing loop were measured as `1` px.

**And a third one, found only because the differ caught the regression the
first two fixes caused.** The first renderer attempt keyed "this table states a
width" on `st.width_px > 0`. A PERCENTAGE width is stored as a NEGATIVE
`width_px`, so `table { width: 100% }` — which is exactly what the `html`
catalog page's stylesheet says at `examples/06_io/ui/web_catalog/html.html:19`
— read as `width: auto` and got shrink-to-fit. Measured consequence: the page's
caption box came out **685 px too narrow and 48 px tall against Chrome's 24**
(it wrapped to two lines), and html went 175 → 196 mismatched. The predicate is
now `st.width_px != 0` and that caption row is gone from the report entirely.

### Fix

- `src/lib/gc_async_mut/gpu/browser_engine/layout_table.spl:203`
  `table_distribute_auto_columns(col_min, col_max, available)` — the CSS 2.1
  §17.5.2.2 distribution as ONE pure function: shrink-to-fit (`available <= 0`)
  takes max-content; `available >= sum(max)` takes max-content plus excess
  proportional to max-content (Chrome's auto-table rule); between the sums each
  column grows by the same fraction of its own min..max range; at or below
  `sum(min)` every column takes min-content. Integer remainder is handed to the
  leading columns so tracks sum EXACTLY to `available`.
- `layout_table.spl:467` `layout_table(node, ctx)` — the M14 lane: per-column
  min/max-content from cell text, colspan distributed over the covered columns
  (only the part they cannot already satisfy), row height = tallest cell,
  `<th>` measured wider for the UA bold default, caption emitted as the table's
  first child box. Exported from `layout.spl`.
- `simple_web_html_layout_renderer_layout.spl:748` `table_cell_max_content_width`
  — delegates to the existing `flex_item_max_content_width` (widest line over
  every in-flow child) rather than growing a second measurement that would
  drift, and replaces both the `width_px <= 0` bail and the `1` px placeholder.
- `simple_web_html_layout_renderer_layout.spl:776` `table_cell_min_content_width`
  — the column FLOOR (longest unbreakable word). Without it a column has
  nothing to compress toward, so a table that does not fit its containing block
  simply overflows. The renderer now calls
  `table_distribute_auto_columns` with both arrays, so the two lanes really do
  resolve columns by ONE function rather than two that drift.
- A CAPMIN clamp (CSS 2.1 §17.5.2: a `width: auto` table is at least as wide as
  its caption's min-content width) was added in the same function. It is
  §17.5.2-correct, but state plainly: it was written on a WRONG hypothesis
  about the caption wrapping (the real cause was the percentage-width misread
  above), **no fixture exercises it**, and it is not what moved any number here.

`rowspan`, `border-collapse` winner widths and percentage column widths are
explicitly NOT modelled and are named as such in the module header.

### Spec: 9/9, and it discriminates

`test/01_unit/browser_engine/table_layout_spec.spl` — 7 pre-existing ACs plus 2
added. **Two fixture corrections were required and are deliberate:**

- The colspan AC asserted `<td colspan=2>wide</td>` wider than `<td>narrow</td>`.
  Under real §17.5.2.2 that is FALSE — "narrow" (6 chars) earns a wider track
  than the two columns "wide" (4 chars) spans, and Chrome renders it that way.
  It passed only under the equal-split fixed-layout rule this lane replaces, so
  the fixture was corrected (longer content in the spanned columns), not the
  algorithm bent to it.
- The first sabotage pass (max-content measurement forced to a constant) left
  all 7 original ACs GREEN — they hold under an equal split too. Two ACs were
  added that actually separate content-based sizing from an equal split: a
  column holding longer text gets a wider track, and a `<th>` measures wider
  than the same text in a `<td>`.

Sabotage (replacing `table_distribute_auto_columns` with the old even
`_compute_col_widths`): exactly those 2 ACs go RED, 7 stay green — so the new
ACs pin the new behaviour and the old ones pin structure.

Neighbouring specs, all unchanged and green on the final tree:
`first_child_top_margin_collapse_spec` 10/10,
`li_marker_nth_path_key_spec` 3/3.
`test/03_system/gui/web_css/web_css_table_replaced_forms_spec.spl` is 5/6 —
the one failure (`button and input render intrinsic widget boxes`) is
**pre-existing**, verified by re-running it with the renderer file reverted to
HEAD and getting the identical verdict.

### Catalog page probes — NOT added, and why

The brief asked for table probes on the catalog pages. `html.html` already
carries a table (the `caption` feature example), and `css-paint.html` one more;
`table`/`tbody`/`td`/`th`/`tr`/`thead`/`tfoot` are all classified `partial` with
no example. Adding probes changes the page, which invalidates the **committed**
Chrome reference geometry the differ compares against — and Chrome's capture is
the thing that times out on this host, so the reference could not be honestly
regenerated in the same round. Deferred rather than landed with a stale
reference; recorded in
`doc/08_tracking/bug/web_table_shrink_to_fit_and_ua_defaults_missing_2026-09-12.md`.

## (2) BOLD ADVANCES — root cause found, fix NOT landed

Round 7 recorded this blocked on "one static bold face tree-wide, Linux-only
font paths". Both halves are retracted by measurement:
`/System/Library/Fonts/Supplemental/Arial.ttf` and `Arial Bold.ttf` are both
present as plain TTFs (no `.ttc`, no `fvar` instancing needed).

The real blocker is `src/lib/nogc_sync_mut/text_layout/font_types.spl:150`:
`font_render_config_valid` returns **false** for any config whose weight is not
`"normal"`, so a bold `FontRenderConfig` is rejected before a face is ever
looked at — while `font_types.spl:123` already folds `weight=` into the render
identity, meaning the metric cache is weight-safe for free. The four-step
closure order is appended to
`doc/08_tracking/bug/web_inline_bold_face_advances_never_selected_2026-09-12.md`.
**No bold delta is reported for this round — none was measured**, because steps
2-4 (bold candidate list, the `st.bold` call site at
`simple_web_html_layout_renderer_core.spl:~3360`, the spec) were not attempted.

## (3) `<li>` reparented geometry desync — root cause established, not fixed

Round 7 left two candidates and established neither. Reading the differ itself
settles it: the Simple side builds its element list **from Draw IR COMMANDS**
(`src/app/ui/chrome_showcase/layout_geometry_diff.spl:191-197` —
`while i < commands.len(): … ids.push(c.component_id); parents.push(c.parent_id)`),
so an element that paints nothing emits nothing and never enters the list. A
plain `<ul>` paints nothing, so the `<li>`'s recorded `parent_id` names a row
that does not exist and the path resolves against the nearest present ancestor,
the `<section>`. The Chrome side walks the DOM and keeps the `<ul>`, so the two
schemes are asymmetric by construction.

That is candidate **(ii)**. Candidate (i) is ruled out: the emitter copies
`nodes[i].parent` faithfully and the parent it copies IS the `<ul>`.

Not fixed here — the repair is to enumerate laid-out elements rather than
painted commands, which changes every page's key scheme at once and wants its
own lane with a full eight-page before/after. Recorded in
`doc/08_tracking/bug/web_geometry_differ_li_reparented_desyncs_nth_paths_2026-09-13.md`.
Consequence for the numbers below: the `html` and `css-layout` absolute counts
are inflated by this desync in EVERY column, before and after alike.

## Per-page geometry differential (lower is better)

All runs at `GEOM_DIFF_HEIGHT=20000`, 8 pages, one worktree, one binary, one
Chrome. **Four runs are reported, not two** — the two intermediate ones are what
found the percentage-width defect, and hiding them would make the final column
look like a clean first try.

- **A** — BEFORE: `origin/main` + the M14-only change (no renderer change).
- **B** — content-sized columns only (`width_px > 0` predicate).
- **C** — B plus the min-content floor, the shared distributor and the CAPMIN
  clamp. **Byte-for-byte the same page numbers as B** — the cap alone moved
  nothing, which is worth knowing before anyone tries it again.
- **D** — C plus the percentage-width fix (`width_px != 0`). This is what lands.

| page | A (before) | B | C | D (landed) | D − A |
|---|---|---|---|---|---|
| overview | 5 | 5 | 5 | 5 | 0 |
| html | 175 | 196 | 196 | 178 | **+3** |
| css-layout | 359 | 359 | 359 | 359 | 0 |
| css-paint | 492 | 493 | 493 | **479** | **−13** |
| forms-media | 101 | 101 | 101 | 101 | 0 |
| animation | 79 | 79 | 79 | 79 | 0 |
| evidence | 0 | 0 | 0 | 0 | 0 |
| tab-bar | 7 | 7 | 7 | 7 | 0 |
| **total** | **1218** | **1240** | **1240** | **1208** | **−10** |

Elements compared: A 1336, B/C 1337, D 1339 — the table pages emit a few more
boxes now. The `css-paint` count rising from 493 to 496 compared while its
mismatches fall by 13 is **not explained here**; it is recorded as such rather
than folded into the story.

The substantive claim is not the page totals, which the `<li>` desync above
inflates on `html` and `css-layout` in every column alike. It is the table rows
themselves: on `html` the table family went from a `caption` box **685 px too
narrow and 24 px too tall** to a single `tbody` row off by `dy=2, dw=1`, with no
`caption` row left in the report at all. On `css-paint`, 13 elements moved onto
Chrome's geometry.

**The `html` +3 is real and is NOT attributed.** `compared` is 253 in both A and
D, so it is not an ordinal artifact; three elements on that page sit further
from Chrome than before. Attribution needs an A/D diff of the two page reports,
which was not run (each full pass is ~17 minutes and the round's budget was
spent). Round 9 should start there.
