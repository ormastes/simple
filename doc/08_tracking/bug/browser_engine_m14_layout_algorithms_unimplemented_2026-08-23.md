# browser_engine M14 layout: types exist, the three layout algorithms were never written

- **Filed:** 2026-08-23
- **Status:** OPEN — genuine missing feature, `@tag:in-development` candidate
- **Found by:** rename/move-drift spec sweep (three `test/*/browser_engine/` specs)

## Claim

`layout_table`, `layout_block`, and `layout_inline` — over the M14
`LayoutContext`/`LayoutBox` type family — **do not exist anywhere in the tree and
never have**. This is not relocation drift. Three specs are blocked on them.

## Evidence that it is absence, not a moved import

1. **Tree-wide grep.** `grep -rn "fn layout_table\b|fn layout_block\b|fn
   layout_inline\b" src/ --include=*.spl` returns exactly ONE hit:
   `src/lib/blink/layout/table_flow.spl:99` — a **different engine**
   (`blink`, not `gc_async_mut/gpu/browser_engine`) with a different type family.
2. **History.** `git log --all -S "fn layout_table(ctx" --
   src/lib/gc_async_mut/` returns **zero commits**. A function that moved leaves
   a deletion; this one has no history at all.
3. **The types ARE there and ARE reachable — proven, not assumed.**
   `layout_m14_types.spl` (73 lines) declares `LayoutContext`,
   `layout_context_new`, `InlineFragment`, `LineBox`, `LayoutBox`, and
   `collapse_margins_signed`, all `pub`. In the same sweep,
   `test/01_unit/browser_engine/margin_collapse_spec.spl` was failing with
   ``function `collapse_margins_signed` not found`` purely because it imported
   from `...browser_engine.layout` (which re-exports none of them) instead of
   `...browser_engine.layout_m14_types`. Repointing that one import took it from
   `ERROR 0/8` to **OK 8/8**. So the M14 module resolves fine — the missing
   thing really is the three algorithms, not the path.
4. **The existing `layout_*.spl` files implement a DIFFERENT, older family.**
   `layout_core.spl` / `layout_table.spl` / `layout_inline.spl` operate on
   `BeDomNode` / `BeLayoutBox` / `FloatContext` (`layout_node`,
   `_layout_block_be`, `layout_flex`, `layout_text_node`,
   `simple_web_fixed_table_*`). `layout_table.spl` has helpers
   (`_collect_table_rows`, `_compute_col_widths`, `_get_colspan`) but **no
   `layout_table` entry point**, and nothing there takes a `LayoutContext`.
   M14 is a newer parallel surface whose types landed and whose algorithms did
   not.

## Blocked specs

| spec (both mirror trees) | needs | status |
|---|---|---|
| `test/01_unit/browser_engine/table_layout_spec.spl` | `layout_table` | ERROR, 0 executed |
| `test/01_unit/browser_engine/anonymous_block_spec.spl` | `layout_block` | ERROR, 0 executed |
| `test/01_unit/browser_engine/ifc_linebox_spec.spl` | `layout_inline` | ERROR, 0 executed |

Each ALSO imports `LayoutContext`/`LayoutBox`/`layout_context_new` from the wrong
module (`...layout` rather than `...layout_m14_types`), exactly like
`margin_collapse_spec` did. That half is mechanical drift — but fixing it alone
would only move the error onto the missing function, so it was deliberately NOT
done: a repoint that leaves the spec red is worse than an honest red, because it
launders a missing feature into what looks like a fixed import.

## What should happen

Either implement the three M14 algorithms, or mark these three specs
`@tag:in-development` with a pointer to this record. Do **not** repoint their
imports in isolation.

## Related

Filed alongside `unresolved_std_text_import_fails_only_at_call_site_2026-08-23.md`
from the same sweep. Same root cause in the small: nothing verifies at import
time that a `use ... .{name}` list is actually exported.
