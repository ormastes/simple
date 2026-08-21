# Stage 1: `unresolved type: BlockValue` in `hir_lowering/module_surface.spl`

Date: 2026-08-21

**Status:** OPEN — root cause narrowed to the enum-payload origin resolver; not
yet reproduced in a fixture, and therefore deliberately NOT fixed. Two candidate
fixes were written and both were reverted for lack of a failing repro (see
"Rejected fixes").

## Symptom

Stage 1 `native-build` of `src/app/cli/bootstrap_main.spl` reports exactly one
occurrence:

```
[hir-fatal] source_idx=14 path=src/compiler/hir/hir_lowering/module_surface.spl
  error_idx=0 text=HIR lowering error in src/compiler/hir/hir_lowering/module_surface.spl:
  unresolved type: BlockValue
```

`module_surface.spl` never names `BlockValue`. It imports `HirExprKind` from
`compiler.hir.hir_definitions`, whose variant

```
CustomBlock(kind: text, value: BlockValue)      # hir_definitions.spl:612
```

carries the payload. `hir_definitions.spl` does not declare `BlockValue`; it
reaches it by an explicit named import at line 11:

```
use compiler.blocks.value.{BlockValue}
```

The terminal declaration is `src/compiler/15.blocks/blocks/value.spl:152`
(`enum BlockValue:`). Note the spelling: the file lives at
`15.blocks/blocks/value.spl`, so its unstripped module name is
`compiler.blocks.blocks.value`, while the import writes
`compiler.blocks.value`. That spelling is the house convention — ten other
files under `15.blocks/` use exactly it, and `15.blocks/__init__.spl:23`
separately re-exports the same name as `compiler.blocks.blocks.value` — so the
short form is not itself the defect, but it is the axis the resolver has to get
right.

## Where it dies

`register_materialized_payload_named_dependency`
(`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl:228`)
walks an imported enum's payload closure. Its second line is

```
val origin = self.resolve_materialized_enum_payload_origin(imported_mod, imported_mod_name, dependency)
if not origin.found: return
```

— a **silent** return. When the origin is not found nothing is materialized, no
diagnostic is emitted here, and the failure only surfaces later as the hard
`unresolved type: {name}` in `hir_lowering/types.spl:811`, attributed to
whichever module imported the ENUM rather than to the type's actual owner. That
misattribution is why the error names `module_surface.spl`, which is innocent.

`resolve_materialized_enum_payload_origin` (same file, :148) has exactly two
steps: the payload owner's own declarations, then one `find_reexport_source`
hop. It has no step for a plain `use other.mod.{Dep}` written by the owner —
unlike its two siblings, `materialize_imported_field_dependency` (:37, three
steps: own declarations, explicit imports, package sibling) and
`materialize_imported_callable_explicit_dependency` (:304).

## Rejected fixes (both reverted)

1. **Add an explicit-import step to `resolve_materialized_enum_payload_origin`,**
   mirroring the callable-signature twin. Written, and it did make a
   three-module fixture (`pv.value` declares `Payload`; `pv.owner` does
   `use pv.value.{Payload}` and declares `enum Event: Wrapped(Payload)`;
   `pv.facade` re-exports; `pv.consumer` globs the facade) resolve the origin —
   **but that fixture already passes WITHOUT the change**, because
   `find_reexport_source` covers it. A fix that only turns green something that
   was never red is not a fix. Reverted.
2. **Rewrite the import in `hir_definitions.spl` to the unstripped
   `compiler.blocks.blocks.value`.** Rejected on inspection: ten sibling files
   use the short spelling and resolve fine, so the short form is valid and the
   rewrite would paper over whatever actually fails.

## Next step for whoever picks this up

The open question is narrow: when lowering `module_surface.spl` in the real
655-module Stage-1 closure, does `imported_mod.import_target_indices` for
`hir_definitions.spl`'s `use compiler.blocks.value.{BlockValue}` hold a valid
surface index, or `-1`?

- If it is **-1**, the defect is module-name resolution in the surface registry
  (the layer-stripped spelling not aliased to the terminal surface), and no
  amount of work inside the payload resolver will help.
- If it is **valid**, the defect is the missing explicit-import step, and fix 1
  above is correct — it just needs a fixture that genuinely reproduces, which
  means driving the real files rather than synthetic three-line modules.

Cheap instrumentation for that question: a level-gated `eprint` at the
`if not origin.found: return` line naming `imported_mod.module_name`,
`dependency`, and the import target indices, then one Stage-1 run.

Harness note, recorded because it cost real time: a spec that drives
`lower_module` over an IMPORTED ENUM dies with
`semantic: method 'lookup_or_invalid' not found on type 'SymbolTable'` before
reaching any of this. `SymbolTable` carries two `impl` blocks in two files
(`hir_types.spl:228` and `hir_symbol_table_methods.spl:18`, the latter holding
`lookup` and `lookup_or_invalid`), and in the interpreted spec context the
second block's methods are unreachable — `SymbolTable.new().lookup("x")` fails
the same way. Calling `resolve_materialized_enum_payload_origin` directly from
the spec sidesteps it and is the workable shape for a unit-level repro.
