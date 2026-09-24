# Chrome ↔ pure-Simple web parity — round 9 (2026-09-13, macOS)

Host macOS (Darwin 25.5.0), binary `build/cargo-r2/release/simple`
(`SIMPLE_EXECUTION_MODE=interpreter`), differ
`scripts/check/check-chrome-layout-geometry-diff.shs` at `GEOM_DIFF_HEIGHT=20000`.
Both sides measured with ONE binary and ONE Chrome per comparison, each in its
own detached worktree at a single commit, per `.claude/rules/testing.md`
§ Measurement traps:

- **A (before)** — `origin/main` @ `482998c47aa` (round 8's landed tree).
- **B (after)** — A plus the two changes below, and nothing else.

## (1) `<li>` desync — round 8's root cause is RETRACTED; it was tree construction

Round 8 concluded the Simple side enumerated Draw IR COMMANDS, so a paintless
`<ul>` emitted no row and every later ordinal shifted. That change was
implemented FIRST (`simple_web_layout_element_geometry_lines` in the renderer,
consumed by `simple_geom_boxes`) and measured alone on the `html` page:
`compared` went **253 → 254**. One row. The other 177 keys still disagreed.

Dumping both key sets settles it. Chrome: `path:0/0/4/2/45/…`. Simple:
`path:0/0/4/11/…` — Simple's tree is one level FLATTER, `<li>` as SIBLING of the
`<ul>`. The divergence begins at the `html:li` feature example,
`<li>…<div class="feature-example"><ul><li>List item</li></ul></div>…</li>`.

`HtmlTreeBuilder` closed the outer `<li>` on the inner one using an **unscoped**
`stack.find_tag("li")`, then `close_through("li")` popped the inner `ul`, the
`div` and the outer `li`; the inner `</ul>` therefore closed the OUTER list and
every remaining `<li>` on the page escaped it. HTML5 "in body" for `li`/`dd`/`dt`
walks the stack DOWN and **aborts at a special element that is not `address`,
`div` or `p`** — an inner `ul` is exactly that barrier.

Fix: `find_tag_in_list_item_scope` + `_html_special_elem` / `_li_scope_barrier`
(`src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl`), applied to
`li`, `dt` and `dd`. Spec `test/01_unit/browser_engine/li_nested_list_scope_spec.spl`
— 5 ACs green; sabotaged back to the unscoped finder, **3 of 5 go RED** (the two
that stay green are the no-barrier cases, which is what they pin).

Both changes land: element enumeration is the correct scheme regardless of its
small yield, because a command list can never be *proved* to cover
`querySelectorAll('*')`, and it is what makes `missing_in_simple = 0` checkable.

### Per-page, before → after

`compared` / `mismatched` (root + inherited) / `missing_in_simple`:

| page | A compared | B compared | A mis | B mis | A root | B root | A inh | B inh | A missS | B missS |
|---|---|---|---|---|---|---|---|---|---|---|
| overview | 18 | 18 | 5 | 5 | 5 | 5 | 0 | 0 | 0 | 0 |
| html | 253 | **431** | 178 | 356 | 118 | 221 | 60 | 135 | **178** | **0** |
| css-layout | 376 | **401** | 359 | 384 | 284 | 289 | 75 | 95 | **25** | **0** |
| css-paint | 496 | **528** | 479 | 511 | 446 | 455 | 33 | 56 | **32** | **0** |
| forms-media | 102 | 103 | 101 | 102 | 46 | 47 | 55 | 55 | 1 | **0** |
| animation | 81 | 81 | 79 | 79 | 59 | 59 | 20 | 20 | 0 | 0 |
| evidence | 4 | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| tab-bar | 9 | 9 | 7 | 7 | 7 | 7 | 0 | 0 | 0 | 0 |
| **total** | **1339** | **1575** | **1208** | **1444** | 965 | 1083 | 243 | 361 | **236** | **0** |

**Read this the right way, and do not read the mismatch total as a regression.**
The mismatch count rises because 236 elements that the differ previously could
not compare at all are now compared, and they mismatch. The honest metric is
`missing_in_simple`: **236 → 0**, i.e. the differ now compares 100% of the
elements Chrome reports, on every page, instead of 82% overall (and 59% on
`html`). No element that was compared before and agreed has stopped agreeing —
`overview`, `animation`, `evidence` and `tab-bar` are byte-identical across A
and B. What changed is that the tool stopped hiding a sixth of the document.

`missing_in_chrome` is 1 on every page in both columns (the `body` row), so the
two enumerations are now the same set plus that one.

### The `html` +3 that round 8 left unattributed

It is not attributable to elements, and the question is now void. Round 8
compared `html` under a key scheme in which **177 of 431 keys resolved against
the wrong ancestor**; A's `compared=253` and D's `compared=253` were equal
counts over a set that did not describe the document. A 3-row delta inside that
space cannot be assigned to three specific elements. The scheme that produced it
is retired by this change; `html` now compares all 431 and is re-baselined at
356 mismatched. No differ pass was spent chasing it.

## (2) BOLD — implemented, measured to be inert, REVERTED, third blocker located

Round 8's step 1 (`font_render_config_valid`'s weight gate) is **not on this
path**: `resolve_font_metrics_with_language` resolves a FAMILY and never builds
a `FontRenderConfig`. Steps 2-4 were implemented on the family axis instead — a
bold candidate list (macOS `Arial Bold.ttf`, Linux DejaVu/Liberation/Nimbus
`-Bold`) carried to both metric call sites as the existing
`__simple_font_face__|<path>|<family>` value, which reaches the measured
advances AND the Draw IR glyph run through one string.

**Measured delta: 0 px.** The probe says why, with a control:

```
load assets/…/NotoSansSC[wght].ttf         -> true   id=sha256=a3041811…;axes=wght=100
load /System/…/Supplemental/Arial.ttf      -> false  id=
load /System/…/Supplemental/Arial Bold.ttf -> false  id=
```

`FontRenderer.try_load_runtime_ttf` **rejects macOS system TTFs outright**,
regular and bold alike, in the same process that loads the bundled asset. Round
8's "both exist as plain TTFs" was true of the files and false of what the
loader accepts. The plumbing was therefore reverted rather than landed: it can
never change an advance here, and on Linux it would swap the FAMILY (Noto →
DejaVu Bold) rather than the weight, which is not parity and is unverifiable on
this host. Landing it would have been dead code with a parity-shaped name.

The pure-Simple route is now named: every bundled candidate is a VARIABLE font
and the resolved identity already carries `axes=wght=100`, so bold is a
`wght=700` INSTANCE of the bundled face — fvar/HVAR instancing in the TTF
loader plus a weight axis on the metric request. Recorded in
`doc/08_tracking/bug/web_inline_bold_face_advances_never_selected_2026-09-12.md`
with two further defects found while measuring and deliberately NOT fixed here
(the language/category override silently discarding explicit `@font-face`
sources; the `"sans-serif".contains("serif")` ordering trap).

## (3) rowspan / border-collapse

Not attempted — the round's budget went to (1) and (2). Unchanged from round 8.

## Specs

- New: `li_nested_list_scope_spec.spl` 5/5 (sabotage 3/5 RED).
- Neighbours, run in BOTH trees with the same binary, **zero delta**:
  `html_tree_builder_flat_projection_spec` 6/6, `li_marker_nth_path_key_spec`
  3/3, `li_last_child_margin_collapse_spec` 12/12,
  `first_child_top_margin_collapse_spec` 10/10, `table_layout_spec` 9/9,
  `html_tree_builder_hardening_spec` 11/13 — the 2 failures are **pre-existing
  and identical** on both sides.
- Pre-existing red, NOT touched: `html_tree_builder_spec.spl` is 8/37 at
  `origin/main` — it calls `be_dom_get_tag_name` (the accessor is
  `be_dom_get_tag`) and `_serialized`, which is defined nowhere in the file. It
  is a broken spec file, not a renderer defect, and fixing it is its own lane.

## Round 10 leads

1. `html` inherited mismatches are 135 of 356 — a single wrong ancestor box
   propagating. Start from `root_mismatched` rows whose children are all
   inherited.
2. `css-paint` 455 root mismatches is now the largest single bucket and is
   unexplained by anything in rounds 7-9.
3. Bold needs variable-font weight instancing; it is not a renderer-lane fix.
