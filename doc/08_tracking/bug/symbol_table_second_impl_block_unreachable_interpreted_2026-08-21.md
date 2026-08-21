# `SymbolTable`'s second `impl` block reported unreachable when interpreted

Date: 2026-08-21

**Status:** RESOLVED — NOT A DEFECT. The reported behaviour does not reproduce;
the real cause is a missing import in the observing spec, and it is neither a
seed-interpreter limitation nor a layout rule the code violates.

## Report

While reproducing `hir_enum_payload_blockvalue_unresolved_2026-08-21.md`, a spec
that drove `lower_module` over an imported enum died with

```
semantic: method `lookup_or_invalid` not found on type `SymbolTable`
```

`SymbolTable` carries two `impl SymbolTable` blocks in two files —
`src/compiler/20.hir/hir_types.spl:228` (the constructor and core mutators) and
`src/compiler/20.hir/hir_symbol_table_methods.spl:18` (`lookup`,
`lookup_or_invalid`, indexing helpers). The report concluded that the second
block's methods are unreachable in an interpreted spec context, citing
`SymbolTable.new().lookup("x")` failing the same way.

## Finding: does not reproduce

`SymbolTable.new().lookup(...)` and `.lookup_or_invalid(...)` both work, in every
import shape tried:

| shape | result |
|---|---|
| `use compiler.hir.hir_types.{SymbolTable}` | PASS |
| `use compiler.hir.{SymbolTable}` (package facade) | PASS |
| `HirLowering.new().symbols` (transitively owned) | PASS |
| `bin/simple run` on a plain script | PASS |

(The original probe's own failure text is worth recording: run directly it
returns `Option::None` from `lookup` and fails only on a bad assertion,
`method 'is_nil' not found on type 'enum'` — i.e. `lookup` had already
dispatched successfully.)

## Actual cause of the observed failure

Method tables are populated only for modules that are IN THE IMPORT CLOSURE.
Importing a TYPE does not drag in every module that carries an `impl` for it. A
spec that names `SymbolTable` without pulling in the module holding the second
block gets `method not found` — correct behaviour, not a merge failure.
`SymbolTable` is immune to this in practice because `hir_types.spl:15` itself
does `use compiler.hir.hir_symbol_table_methods.*`, so any import of `hir_types`
(direct, facade, or transitive) brings both blocks.

The same class DID bite the sibling investigation for a different type:
`resolve_materialized_enum_payload_origin` is `method not found on type
'HirLowering'` until the spec adds `use compiler.hir.hir_lowering.items.*`,
because that method's `impl HirLowering` block lives in
`_Items/module_reexport_materialization.spl`. `HirLowering` has 23 `impl` blocks
across as many files and `CompilerDriver` has 20, so cross-file `impl` blocks are
a pervasive, working pattern in this tree — a genuine failure to merge them would
break far more than one method.

## Disposition

No seed change (`src/compiler_rust/**` untouched) and no impl-block merge. The
blocks stay split as documented in `hir_symbol_table_methods.spl`'s header.
Blast radius check: `^impl SymbolTable` = 2 files; multi-file `impl` counts
across `src/compiler` are led by `HirLowering` (23), `CompilerDriver` (20),
`MirLowering` (11), `HmInferContext` (9) — all functioning.

## Regression spec

`test/01_unit/compiler/hir/symbol_table_cross_file_impl_spec.spl` (byte-identical
mirror at `test/unit/compiler/hir/...`) pins all three import shapes above so a
real future merge failure is caught. 3 examples, 0 failures.
