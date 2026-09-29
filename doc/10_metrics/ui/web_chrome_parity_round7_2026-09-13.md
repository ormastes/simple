# Chrome ↔ pure-Simple web parity — round 7 (2026-09-13, macOS)

Host: macOS (Darwin 25.5.0), worktree
`.claude/worktrees/agent-aabafaf9bfca3aa6a`, binary
`build/cargo-r2/release/simple` (interpreter execution mode), Chrome
`/Applications/Google Chrome.app`. Pixel differ
`scripts/check/check-chrome-catalog-pixel-diff.shs` at 900x760; geometry differ
`scripts/check/check-chrome-layout-geometry-diff.shs` at `GEOM_DIFF_HEIGHT=20000`.

**Both sides of the A/B were measured in THIS worktree with THIS binary**, per
`.claude/rules/testing.md` § Measurement traps ("never A/B across two trees").
BEFORE = the same tree with only the two `src/lib/.../browser_engine/*.spl`
files checked out at `HEAD~1`; AFTER = the same tree with them restored.
Nothing else differs. The round-6 figures quoted in the round-7 brief were
measured on another host and are NOT used as the before column.

## Items

### (d) nth-path desync inside `<li>` — FIXED, but not the item the brief described

The brief's framing ("the differ's DOM path for list items skips the
`::marker`") was already closed on 2026-09-12 in the differ itself
(`_layout_tag` excludes `::`-prefixed tags). What was still open is the
**renderer's own copy of the same scheme**:

- Root cause: `_simple_web_layout_element`,
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:124`
  — skipped `#text`/`style`/`script`/`title`/`head`/`meta`/`link`/`base` but not
  `::marker`, which the foundation pass synthesises as every `<li>`'s FIRST
  child (`..._foundation.spl:1128`, "First child by construction"). The Chrome
  walker in `check-chrome-layout-geometry-diff.shs:80-82` claims these mirror
  each other "byte-for-byte"; they did not. Every hit-test and CSS-animation
  target key for an element inside an `<li>` was off by one ordinal.
- Fix: exclude any `::`-prefixed tag there too, so the Chrome walker, the
  geometry differ and the renderer now agree.
- Spec: `test/01_unit/browser_engine/li_marker_nth_path_key_spec.spl` (3 AC).
- This does NOT affect the pixel differ (it keys nothing) and does not move the
  per-page numbers below; it is a correctness fix on the interaction path.

**Still open and NOT this defect:** `<li>` boxes attributed to the enclosing
`<section>` rather than the `<ul>`, which is what actually desyncs the geometry
report on `html` after `path:0/0/4/3` —
`doc/08_tracking/bug/web_geometry_differ_li_reparented_desyncs_nth_paths_2026-09-13.md`.
Round 7 narrowed it by one step but did NOT establish the root: Draw IR
parentage is copied straight from `nodes[i].parent`
(`..._paint_layout.spl:3117-3125`), so the emitter itself does not invent a
parent. Two candidates remain live and neither is established — (i) the parsed
tree really does give the `<li>` the `<section>` as parent, or (ii) the `<ul>`
emits no Draw IR command (invisible / no paint) and the differ's own
`_index_of_id` / `_seen` handling of a missing intermediate ancestor produces
the shift. Not closed in round 7.

### (a) first-child TOP margin collapse-through — FIXED

- Root cause: `simple_web_html_layout_renderer_layout.spl` — the caller advances
  `cy` by `collapse_margins_signed(prev_margin_b, cst.margin_t)` BEFORE
  `layout_with_style` runs, so the round-6 trailing-margin shape
  (`trailing_margin_b`, known only after the children are laid out) could not be
  mirrored.
- Fix: `LayoutResult.leading_margin_t` + `block_top_margin_collapses_through`
  (exclusion set mirrored from the bottom half) + a two-phase correction using
  the existing `offset_layout_subtree`: the child is placed from its DECLARED
  margin-top, then re-offset by the difference against its EFFECTIVE one
  (`collapse(declared, child.leading_margin_t)`). When the block itself
  collapses through, the whole effective margin is pulled back out, the height
  shrinks by it, and it is returned for the parent to collapse — so N nested
  wrappers yield ONE margin.
- Specs: `test/01_unit/browser_engine/first_child_top_margin_collapse_spec.spl`
  (10 AC: 3 reproducing + 7 generalization, incl. `<li>`/`::marker` and an
  out-of-flow first child). Sabotage: forcing the predicate to `false` fails
  AC-1/2/3/8 and leaves AC-4..7 green.
- Record: `doc/08_tracking/bug/web_first_child_top_margin_never_collapses_through_2026-09-13.md`
  flipped to FIXED with the mechanism and the sabotage triple.

### (c) bold advances — re-confirmed BLOCKED, not attempted

Re-verified on this macOS host rather than taken on trust: `find assets -iname
"*Bold*"` returns exactly one face tree-wide (`UnifrakturCook-Bold.ttf`,
blackletter display), and `browser_sans_font_candidates`
(`src/lib/nogc_sync_mut/text_layout/font_provider.spl:68-77`) otherwise lists
bundled VARIABLE fonts plus `/usr/share/fonts/...` Linux regular faces that do
not exist on macOS at all. Step 1 of the closure order (a static bold candidate
list, or `fvar` instancing in the TTF loader) is still in files this lane does
not own; adding the weight argument first would change no advance and would be
unused code. Round-7 note appended to
`doc/08_tracking/bug/web_inline_bold_face_advances_never_selected_2026-09-12.md`.

### (b) tables — not started

`table_layout_spec` 0/7 is a multi-hour item on its own and was correctly
deprioritised behind (d)/(a) per the brief's own ordering. Existing record:
`doc/08_tracking/bug/web_table_shrink_to_fit_and_ua_defaults_missing_2026-09-12.md`.

## Per-page geometry differential (lower is better)

**The pixel differ could not be run on this host.** Chrome hits the 90 s
`--screenshot` alarm on every catalog page, and one `html` Simple render had
still not produced a `.ppm` after 20 minutes — in BOTH lib states, so it is the
host, not the change. Two attempts were made (full catalog, then a 3-page
subset) and both were abandoned. The brief's stop criterion ("html/css-layout/
animation each drop by >=2 pixel points") is therefore **unevaluable in this
round**; it is not reported as met or unmet. The geometry differ is substituted
because it renders Draw IR without rasterising.

| page | compared | mismatched BEFORE | mismatched AFTER | delta |
|---|---|---|---|---|
| css-layout | 376 | 359 | 359 | 0 |
| animation | 81 | 79 | 79 | 0 |

`css-layout.geometry_diff.md` is **byte-identical** between the two runs
(`diff -q` rc=0; total |dy| over the 200 root-mismatch rows is 38114 on both
sides). That is a real result, not a failed measurement: the page carries 113
elements with a 16 px top margin, but the collapse-through predicate excludes
flex/grid items and any parent with top padding or a border, which is what a
card-based CSS demo page is made of. The two fixes are pinned by the
oracle-backed specs below, not by this page.

Both sides used the same worktree, the same binary and the same Chrome; the
BEFORE side differs only by `git checkout HEAD~1 --` on the two
`browser_engine` lib files.

## Neighbouring specs

| spec | result |
|---|---|
| `li_last_child_margin_collapse_spec` (round-6 twin) | 12/12 |
| `anonymous_block_spec` | 4/4 |
| `layout_paint_contract_pin_spec` | 6/6 |
| `inline_content_area_half_leading_spec` | 4/4 |
| `flex_wrap_auto_width_item_spec` | 4/4 |
| `grid_repeat_minmax_track_list_spec` | 4/4 |
| `inline_run_advance_and_break_boxes_spec` | 5/5 |
| `layout_text_node_spec` | 4/4 |
| `ifc_linebox_spec` | **0/10 — PRE-EXISTING**, fails identically with the two lib files reverted to `HEAD~1`; not caused by this change |
