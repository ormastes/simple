# `grid-template-areas` and `grid-auto-flow` are entirely unimplemented in the browser engine

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

- **Filed:** 2026-08-07
- **Severity:** P2 — no crash; named-area placement and column-first
  auto-placement simply do not happen. Cells fall back to the default
  row-major auto-placement algorithm regardless of these declarations.
- **Affects:** any CSS using `grid-template-areas` + `grid-area`, or
  `grid-auto-flow: column` (or `dense` variants).
- **Found by:** `test/03_system/gui/web_css/web_css_grid_spec.spl` — examples
  `"grid-template-areas places named cells (RED-by-design)"` and
  `"grid-auto-flow: column fills column-first (RED-by-design)"` (see that
  spec's file:line), part of unit U3.3 of
  `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`.

## Root cause

`grep -rn "grid-template-areas\|grid_template_areas\|grid-auto-flow\|grid_auto_flow"
src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_*.spl`
returns **zero matches**. Neither property is parsed by the CSS declaration
layer nor consulted by the Grid placement code in
`simple_web_html_layout_renderer_layout.spl` (the auto-placement loop around
line 1462 onward always walks candidate cells in row-major order —
`candidate_row = candidate / grid_column_count`, `candidate_column =
candidate % grid_column_count` — with no branch for a column-first mode).

Concretely:
- `grid-template-areas: "left right"` plus `grid-area: right` on a child is
  silently ignored; the child is placed by the default auto-placement
  algorithm instead of by name, landing in the first available track
  (probed: `x=0`, not the named `right` track's `x=20`).
- `grid-auto-flow: column` is silently ignored; a third auto-placed cell in
  a 2x2 grid lands row-first in row 2 column 1 (`x=0,y=10`) instead of
  column-first in column 2 row 1 (`x=10,y=0`).

## Unblock condition

1. Parse `grid-template-areas` (a sequence of quoted row strings) into a
   named-area-to-track-range map, and `grid-auto-flow` into a flow-mode enum
   (`row` | `column`, with an optional `dense` modifier).
2. In the placement loop, resolve `grid-area`/`grid-row`/`grid-column`
   named-area references against that map before falling through to
   numeric/auto placement.
3. Make the auto-placement candidate-cell walk branch on flow mode: row-major
   (existing) vs column-major (iterate `candidate_column` before
   `candidate_row`).

Once landed, flip both RED-by-design examples in
`test/03_system/gui/web_css/web_css_grid_spec.spl` to assert the real
named-area / column-first geometry and drop the `(RED-by-design)`
qualifier from their names.

## Status

RESOLVED (2026-08-08) — with noted simplifications.

Both properties are now parsed and consulted by the placement code:

- `normalized_grid_template_areas`, `normalized_grid_area`, and
  `normalized_grid_auto_flow`
  (`simple_web_html_layout_renderer_declarations.spl`) parse
  `grid-template-areas` (quoted row strings, rejecting non-rectangular row
  shapes outright), `grid-area` (named-reference form only — the numeric
  `row/col/row-end/col-end` shorthand is out of scope), and `grid-auto-flow`
  (`column` flow only — no `dense` modifier).
- `grid_template_area_rects` (`simple_web_html_layout_renderer_layout.spl`)
  resolves the parsed template into per-area-name rectangles, validating
  that each name's occupied cells form a solid rectangle (CSS Grid SS7.1) —
  a non-rectangular name is dropped silently, per this renderer's existing
  lenient-CSS convention, and a `grid-area` reference to a dropped name
  falls through to numeric/auto placement. A child with `grid-area:<name>`
  matching a resolved rectangle has its column/row start and span set from
  that rectangle before the existing clamp/auto-placement logic runs.
- The auto-placement candidate-cell walk now branches on
  `st.grid_auto_flow_column`: column-major (`candidate_column` before
  `candidate_row`), bounded by the explicit row-track count from
  `grid-template-rows` when one is declared (matching browser behavior for
  a grid with a fixed row count), rather than the row-major capacity buffer
  sized for implicit-row growth.

**Noted simplifications** (left as-is; not required by the unblocking spec
examples):
- No `.` dot-cell handling beyond treating it as an empty/unnamed cell.
- No implicit-track creation beyond what the template's own row/column
  count implies.
- No `grid-auto-flow: dense` (packing back to fill earlier gaps).
- No numeric `grid-area` shorthand (`grid-area: 1 / 1 / 2 / 2`) — only the
  named-area reference form.
- When `grid-auto-flow: column` is set but no `grid-template-rows` is
  declared, column-major placement falls back to the row-major capacity
  buffer as its row bound (no spec example exercises this combination).

`test/03_system/gui/web_css/web_css_grid_spec.spl`'s
`"grid-template-areas places named cells"` and `"grid-auto-flow: column
fills column-first"` examples (previously `"...(RED-by-design)"`) now
assert the real named-area / column-first geometry and pass.

**Follow-up fix (2026-08-08):** `normalized_grid_area`
(`simple_web_html_layout_renderer_declarations.spl`) was lowercasing the
`grid-area` ident (`raw.trim().lower()`) while `normalized_grid_template_areas`
preserved the template cells' case verbatim — so `grid-area: Sidebar` never
matched a template cell `"Sidebar"` and silently fell to auto-placement.
CSS grid-area/named-line idents are case-sensitive (only the `auto` keyword
is case-insensitive). Fixed by dropping `.lower()` from the returned value
and comparing only the `auto` check case-insensitively. New example
`"grid-template-areas/grid-area matching is case-sensitive"` in
`web_css_grid_spec.spl` covers a mixed-case `"Header Header"` template
against `grid-area:Header`, asserting placement (not auto-placement
fallback). Full suite: 7/7 passing.

## 2026-08-07 triage note (web_css RED sweep)

Scope estimate: **large** — two independent unimplemented subsystems bundled
under this one bug record: (1) `grid-template-areas`/`grid-area` named-cell
placement needs a template-string parser plus an area-name-to-cell map
consulted before auto-placement; (2) `grid-auto-flow: column` needs the
auto-placement candidate-cell walk to branch on flow mode (column-major vs
the existing row-major only). Both are zero-occurrence in
`simple_web_html_layout_renderer_*.spl` per the file-level grep already
recorded above — new code, not a bug in existing code. Not attempted this
session — picked the narrower `text-overflow: ellipsis` Draw IR gap instead
(single call-site fix, see
`web_css_text_overflow_ellipsis_draw_ir_gap_2026-08-07.md`). Left RED,
untouched.
