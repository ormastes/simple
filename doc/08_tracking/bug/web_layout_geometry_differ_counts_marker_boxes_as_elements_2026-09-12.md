# The layout geometry differ numbered `::marker` boxes as elements

- Status: FIXED 2026-09-12
- Area: `src/app/ui/chrome_showcase/layout_geometry_diff.spl`
- Found by: reading signed per-element deltas on a minimal `<ul><li>` fixture

## Symptom

On any page with `<li>` elements the differ reported enormous, physically
impossible deltas for the `<li>`'s children. On
`test/fixtures/browser_engine/layout/round3_probe.html` it reported the first
`<code>` inside an `<li>` as **119 px too wide and 85 px too tall**, when the
element's real disagreement with Chrome is 5 px wide and 1 px tall.

## Root cause

Both sides key on a body-relative nth-path over "layout elements". The Chrome
side is a `querySelectorAll('*')` walk, so it sees **elements only**. The Simple
side accepted every Draw IR box carrying a `tag`, including the `::marker`
pseudo box the renderer emits as the **first** child of every `<li>`.

So Chrome's `li > *:nth(0)` (the real first element, the `<code>`) was compared
against Simple's marker box, and every later sibling was off by one as well —
each `<li>` contributing 2-3 entirely fabricated mismatch rows. The catalog's
feature-inventory pages carry ~100 `<li>` each.

F20's round-2 metrics note had predicted exactly this — *"These do not shift
ordinals today (markers are last children) but will the moment a marker is
emitted first"* — the premise had simply already stopped being true.

## Fix

`_layout_tag` excludes any tag beginning `::`. Marker boxes are still counted
and listed under "Simple-only boxes", so nothing is hidden — they are removed
from the KEY SCHEME only.

## Consequence for reading the numbers — read this before comparing runs

This changes what the differ measures, so mismatch counts before and after are
not directly comparable. Correcting the keys makes previously-unmatched `<li>`
children align and be COMPARED, which moves them out of "missing in Simple" and
into the compared population — where most of them still mismatch for unrelated
block-flow reasons. On `html.html` the compared population rose 202 -> 253 and
the raw mismatch count rose with it. That is a measurement correction, not a
regression, and the round-3 metrics table states both figures rather than
quoting only the flattering one.

## Sabotage triple

1. Baseline: the probe fixture reports the `<code>` row as `dw 5, dh 1`.
2. Remove the `not tag.starts_with("::")` clause: the same row reports
   `dw 119, dh 85`, and the `<p>` sibling reports `dw 730`.
3. Restore: `dw 5, dh 1` again.

## Round 7 (2026-09-13) — the SECOND copy of the key scheme had the same defect

The 2026-09-12 fix corrected `_layout_tag` in the differ. It did not correct the
renderer's own copy: `_simple_web_layout_element`
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:124`),
which feeds `_simple_web_node_target_key` and the bulk animation target-key
pass, skipped `#text`/`style`/`script`/`title`/`head`/`meta`/`link`/`base` but
NOT `::marker` — while the geometry differ's walker comment claims the two
mirror each other "byte-for-byte". They did not: every hit-test and CSS
animation target key for an element inside an `<li>` was off by one ordinal, so
a pointer event or an animation keyed by path addressed the wrong node.

Fixed by excluding any `::`-prefixed tag there too, so all three copies of the
scheme (Chrome walker, differ, renderer) now agree.

Spec: `test/01_unit/browser_engine/li_marker_nth_path_key_spec.spl` — AC-1 the
block inside an `<li>` is `path:0/0/0`, AC-2 a second element child keeps
ordinal 1, AC-3 a block outside any list is unaffected. Sabotage (swap `"::"`
for a string no tag starts with): AC-1 and AC-2 fail, AC-3 still passes.
