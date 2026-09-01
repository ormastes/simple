# layout_core still targets the pre-redesign BeLayoutBox (2026-08-15)

**Status:** open
**Area:** `src/lib/gc_async_mut/gpu/browser_engine/layout_core.spl` vs
`layout_box.spl`
**Spec blocked:** `test/01_unit/browser_engine/layout_text_node_spec.spl` — 0/4

## Summary

`layout_box.spl` ships the redesigned `BeLayoutBox` (fields `node_id`, `kind`,
f64 geometry, `tag_name`, `style`; `content_x`/`content_width` are METHODS),
but `layout_core.spl` still constructs the OLD shape at 10 sites:
`BeLayoutBox(x: ..., content_x: ..., content_width: ..., node: ..., ...)` —
e.g. `layout_text_node` (`layout_core.spl:595`+). Any call into those paths
fails with `semantic: class BeLayoutBox has no field named 'content_x'`.
This predates the 2026-08-11 tree wipe/restore (`6f86ff32a7d` /
`ae55a746719`): the same mismatch exists at `6f86ff32a7d~1`, so it is a
half-landed refactor, not restore damage.

`layout_text_node_spec.spl` additionally imports
`layout_core.layout_text_node` with the old signature and constructs the old
`BeLayoutBox` itself, and imports `layout_text_has_break_opportunity`, which
does not exist anywhere in the tree (`grep -rn layout_text_has_break_opportunity
src/lib` → 0 defs).

## Repro

```
bin/simple test test/01_unit/browser_engine/layout_text_node_spec.spl --no-session-daemon
# ✗ semantic: class `BeLayoutBox` has no field named `content_x`
# ✗ semantic: function `layout_text_has_break_opportunity` not found
```

## Related, fixed in the same triage session

The sibling M14 layout specs (`anonymous_block_spec`, `table_layout_spec`,
`margin_collapse_spec`, `ifc_linebox_spec`) were RED for a different reason — the M14 spec-facing
API (`layout_block(doc, LayoutContext)`, `layout_table`, `layout_context_new`,
`collapse_margins_signed`) existed only as types in `layout_m14_types.spl`
with no implementations and no re-export from `browser_engine.layout`. Those
functions are now implemented in `layout_m14_types.spl` and re-exported from
`layout.spl`; all three specs are GREEN. This record covers only the
`layout_core` / `BeLayoutBox` reconciliation, which is a real refactor:

## Unblock condition

Port `layout_core.spl` (10 ctor sites plus all `container.content_*` reads)
to the committed `BeLayoutBox` shape, implement
`layout_text_has_break_opportunity` (whitespace break-opportunity scan), and
update `layout_text_node_spec.spl` to the ported signatures.
