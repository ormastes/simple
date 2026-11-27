# HIR import resolution: two pre-existing reds in resolve_import_symbols_spec

- **Date:** 2026-11-13
- **Status:** open
- **Area:** `src/compiler/20.hir/hir_lowering/` (module surfaces / import registration)
- **Spec:** `test/01_unit/compiler/hir/resolve_import_symbols_spec.spl` (36/38 on the Rust seed)

Both examples already fail at 4aac96a7a4c (2026-11-04). The other three
failures from the 2026-11-12 sweep were stale expectations and were
retargeted (W-HIR-UNDECL-IMPORT-001 recovered warning from 54356c20894;
tail call in `HirBlock.value`).

## 1. Unbraced renamed re-export publishes no export origin

Example "resolves an unbraced renamed re-export to its defining function".
The facade `export use alias.provider.orig as public_orig` records the
import target `alias.provider` and the item `orig`. The resolution trace
selects `alias.provider` correctly. But `facade_surface.export_origins` is
empty, so `export_origins["public_orig"]` is nil, and the example fails with
"undefined field 'owner_module' ... on value of type 'nil'". The braced
spelling is the control, and it works.

## 2. A module alias leaks its members into the bare namespace

Example "keeps a complete module alias when that module exists". After
`use alias.provider as p`, the consumer's symbol table also binds a bare
`orig`. Instrumented, that binding is a `SymbolKind::Function` with
`defining_module == alias.provider`. Only `p` and `p.orig` should be bound,
so `lookup_or_invalid("orig").is_valid()` should be false.
