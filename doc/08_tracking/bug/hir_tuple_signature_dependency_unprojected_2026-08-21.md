# HIR: a TUPLE in an imported signature bypassed qualified-scope projection

- **Date:** 2026-08-21
- **Status:** FIXED
- **Severity:** blocker (Stage 1 self-compilation)

## Symptom

```
[hir-fatal] source_idx=1 path=src/compiler/driver/driver.spl error_idx=1
text=HIR lowering error in src/compiler/driver/driver.spl: unresolved type: ResolveError
```

`src/compiler/80.driver/driver.spl` never names `ResolveError` — 0 hits across
all 156 lines. The error was attributed to an innocent importer.

## Root cause

`struct ResolveError` is declared at `src/compiler/35.semantics/resolve.spl:762`
and `fn resolve_methods` (`:775`) returns the TUPLE
`(HirModule, [ResolveError])`.

Cross-module signature dependencies are materialized under the QUALIFIED local
name `{module}::{name}` — verified live with a trace on
`register_imported_symbol`, which logged
`mod=sem.resolve name=ResolveError local=sem.resolve::ResolveError` — never the
bare name. The importer's plain scope therefore does not contain `ResolveError`,
by design.

Projecting an imported signature back through the declaring module's qualified
scope is `imported_surface_type_projected`
(`src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl:166`). It
handles exactly two SCALAR shapes: `type_name` (a top-level named type) and
`array_element_name` (an array of a named type). A tuple populates NEITHER, so
it fell to `imported_surface_type` (`:157`), which likewise projected only a
top-level `Named` kind, and finally to `lower_type` — which resolves names in
the IMPORTER's scope and lands on the hard, non-recovered
`unresolved type: {name}` at `hir_lowering/types.spl:811`.

The defect is **shape-specific, not type-specific**: the same signature written
as a bare `[ResolveError]` always resolved, because that populates
`return_array_element_name`. That is what made the failure look arbitrary — of
`CompileResult`'s eight variant payload types only `ResolveError` was reported,
and it had nothing to do with `CompileResult` at all.

## Fix

`imported_surface_type` now projects COMPOSITE shapes elementwise instead of
falling straight through:

- a tuple recurses per element through `imported_surface_type` and rebuilds
  `HirTypeKind.Tuple`;
- an array of a named element takes the same qualified lookup the scalar
  `array_element_name` branch already used;
- everything else keeps the previous `lower_type` fallback.

`parser_type_kind_tuple_elements` / `parser_type_kind_array_element_name` are
used for decoding — both already return an empty result for a non-matching
kind, so no discriminant dispatch is added in an HIR scope (where `TypeKind`
and `HirTypeKind` variant names collide).

A level-gated advisory
(`SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE=1`, `[hir-callable-composite-return]`) was
added to `materialize_imported_callable_type_dependencies` so a composite
return that materializes ZERO named dependencies is observable rather than
silent.

## Reproduce spec

`test/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.spl`
(byte-identical mirror at `test/unit/compiler/hir/...`). Two cases: the tuple
shape, and the array shape as a control.

- pre-fix: `outcome=ERROR ... passed=1 failed=1`, `unresolved type: ResolveError`
  on the tuple case, control green — pinning the shape claim.
- post-fix: `outcome=OK ... passed=2 failed=0`.

Neighbours still pass: `enum_payload_origin_plain_use_spec.spl`,
`imported_composite_field_package_sibling_spec.spl`,
`enum_shortname_collision_two_owners_spec.spl`.
