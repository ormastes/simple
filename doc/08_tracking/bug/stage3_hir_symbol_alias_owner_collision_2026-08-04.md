# Stage 3 HIR `Symbol` alias owner collision

Status: superseded repair strategy; the terminal-identity fix is tracked in
`stage3_symbol_alias_payload_identity_conflict_2026-08-04.md`.

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

## Superseded fix claim

This record previously claimed that deleting `type Symbol = HirSymbol` and
migrating every consumer was the canonical repair. History disproves that
claim: commit `2043f80114` intentionally renamed the physical structure to
`HirSymbol` while retaining `Symbol` as a compatibility alias, and the later
source-reading test that demanded deletion did not change the implementation
or its consumers.

The current repair preserves `HirSymbol` as the concrete owner and `Symbol` as
the compatibility surface. HIR materialized-payload identity terminalizes a
non-generic same-module alias to its concrete target before collision checks,
so alias spelling cannot create a second declaration identity. Unrelated
module-local aliases such as `type Symbol = text` remain intact.

## Regression contract

`test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl`
checks the physical owner plus compatibility export, while
`test/03_system/native/hir_materialized_enum_payload_dependencies.spl` covers
the exact alias-to-composite terminalization and a genuine adjacent collision.

## Deferred evidence

A future bootstrap lane may rerun Phase 3 once its own bounded cycle budget is
available. Required evidence is a real Stage 3 executable and an explicit
successful build log; shell-wrapper exit status alone is insufficient.
