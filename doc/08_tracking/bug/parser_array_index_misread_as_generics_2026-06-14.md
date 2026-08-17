# Bug: array indexing `name[expr]` misread as `[...]` generics in some contexts

- **ID:** parser_array_index_misread_as_generics_2026-06-14
- **Severity:** P2 (blocks loading `common.ui.style`, hence the slides/word GUI
  widget render chain, from new dependents)
- **Discovered:** 2026-06-14, wiring slides render to the office style resolver
- **Status:** CLOSED 2026-08-17 — the parser false positive no longer fires.
  See "Verdict 2026-08-17" at the end.

## Summary

`src/lib/common/ui/style.spl:559-560` indexes a local array with
`matched[j]` / `matched[j + 1]`. The current parser/generics-migration pass
reads `matched[...]` as a `[...]`-style generic type application and errors:

```
559 |  while j >= 0 and current.selector.specificity < matched[j].selector.specificity:
    |                                                          ^
Use angle brackets: matched<...> instead of matched[...]
Run `simple migrate --fix-generics` to automatically update your code
```

Because this is a load-time parse error, any module that transitively imports
`common.ui.style` (e.g. `app.office.slides.render` via `common.ui.widget`)
fails to load.

## Why this is a parser bug, not a source bug

`matched[j]` is ordinary array indexing, not generics. The `[...]`→`<...>`
generics migration heuristic should not fire on `identifier[expr]` where the
identifier is a value (array) rather than a type. Rewriting the source to
`matched.get(j)` would be silently normalizing around a parser defect, which the
project rules say to avoid — so this is filed instead.

## Workaround in use

The new slide HTML renderer was placed in a separate file
(`src/app/office/slides/html_render.spl`) that imports only the slide model and
the office style resolver, avoiding the `common.ui.widget` → `common.ui.style`
chain. That path is a pure model→CSS→HTML transform and loads/verifies cleanly.

## Proposed fix

Make the generics-migration / parser disambiguation treat `identifier[expr]` as
indexing (not a generic) when `identifier` resolves to a value binding, or when
the bracket contents are an expression rather than a type. Then `common.ui.style`
loads without edits.

## Further occurrence — 2026-07-27, vhdl_gen

Still reproducing, now in the RTL generator. `src/lib/hardware/vhdl_gen/tb_single_lane_types.spl:182`

```simple
while k < rows[r]:          # rows is a fn parameter of type [i64]
```

emits, twice per run:

```
Use angle brackets: rows<...> instead of rows[...]
```

Repro: `bin/simple run test/01_unit/lib/hardware/vhdl_gen/probe_tb_single_lane_gen.spl`

Non-fatal here — the probe still reports `ALL PASS` and all five generated
testbenches stay byte-identical to their goldens — so this occurrence is noise,
not a blocker. Recorded rather than worked around: the natural fix would be to
rename or restructure the parameter, which would be normalizing a compiler
defect into the source.

Note this instance narrows the trigger usefully (see verdict below): `rows` here is a **function
parameter** declared `rows: [i64]`, not a local `var`. So the disambiguation
fails for parameter bindings too, not just locals — worth covering in whatever
fix lands. Sibling report: `u8_index_generics_deprecation_false_positive_test_path_2026-06-28.md`.

## Verdict 2026-08-17: CLOSED — no longer reproduces (closed on content/behaviour)

Ran this doc's own designated reproducer, which it recorded as emitting the
diagnostic **twice per run**:

```
$ bin/simple run test/01_unit/lib/hardware/vhdl_gen/probe_tb_single_lane_gen.spl
rc=0
$ grep -c "angle brackets" <output>
0
```

Zero occurrences. `rows` at `src/lib/hardware/vhdl_gen/tb_single_lane_types.spl:182`
is still a function parameter declared `rows: [i64]` and is still indexed as
`rows[r]` — i.e. the trigger source is unchanged and the parser simply no longer
misfires on it. The narrowed parameter-binding trigger recorded above is
therefore covered.

The original P2 blocker is also gone: a module doing `use std.common.ui.style.*`
loads with **0** angle-bracket diagnostics.

Caveat, so this close is not read as broader than it is:
`src/lib/common/ui/style.spl:555-565` no longer contains the `matched[j]` /
`matched[j + 1]` indexing quoted in the Summary — the sort was rewritten into an
insertion loop over `matched`. That rewrite is **not** a workaround for this
parser bug; the in-source comment attributes it to a different defect
("Avoid indexed assignment here because native entry-closure builds reject it on
this path"). So `style.spl` is no longer usable as evidence either way, and this
close rests entirely on the vhdl_gen reproducer, whose trigger is intact.

Unrelated observation, not this bug: that probe now ends
`TB_SINGLE_LANE PROBE: 1 FAILURES` (a golden/determinism mismatch, not a parse
error). It is outside this doc's subsystem and was not investigated here.
