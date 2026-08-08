# Stage 3 HIR `Symbol` alias owner collision

Status: fixed in the pure-Simple HIR ownership boundary; Phase 3 rerun intentionally deferred.

## Failure

The bounded Phase 3 bootstrap reached `driver_source_loading.spl` and rejected
its dependency surface twice:

```text
enum payload dependency `Symbol` conflicts:
compiler.hir.hir_types::Symbol::struct vs
compiler.hir.hir_types::Symbol::type_alias
```

Evidence: `/tmp/simple-phase3-rebuild-cycle3-20260804.log`. That session had
already reached its mandatory three-cycle cap, so this change does not claim a
new Phase 3 artifact.

## Cause

`hir_types.spl` declared the concrete `HirSymbol` structure and then exported
the legacy alias `type Symbol = HirSymbol`. Local type-alias registration now
preserves aliases during HIR lowering. The Stage 3 dependency collector could
therefore see the legacy alias and its concrete target as two declaration
kinds for the same exported dependency identity.

## Fix

`HirSymbol` is now the sole symbol-table entry owner and exported name. HIR,
trait, visibility, MIR, and interpreter consumers use that concrete name.
Unrelated module-local aliases such as `type Symbol = text` remain intact; the
fix does not disable or discard type aliases globally.

## Regression contract

`test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl`
checks the sole-owner export, concrete consumer annotations, and preservation
of an adjacent local alias. The existing backend declaration-collision spec was
updated to reject reintroduction of the legacy HIR alias.

## Deferred evidence

A future bootstrap lane may rerun Phase 3 once its own bounded cycle budget is
available. Required evidence is a real Stage 3 executable and an explicit
successful build log; shell-wrapper exit status alone is insufficient.
