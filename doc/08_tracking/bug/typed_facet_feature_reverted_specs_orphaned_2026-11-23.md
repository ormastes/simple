# Typed-facet feature reverted; its specs were left behind — 2026-11-23

Status: open — OWNER DECISION needed (restore the feature or delete the specs).
Owner: src/compiler/{10.frontend,20.hir,35.semantics,80.driver}, src/lib/common facet modules.

`test/01_unit/compiler/hir/facet_hir_codec_compat_spec.spl` ran 0 examples on
release/1.0.0: `cannot resolve import common.facet_abi` (E1034). Its other
dependencies are gone too. `HirFacetAcquireMode`, `HirModule.facet_interfaces`,
`HirExprKind.FacetAcquire`, MethodCall `type_args` and
`parser_set_aspect_context` have zero hits in `src/` on both release/1.0.0 and
origin/main.

Cause: fcbec1c3b62 (2026-08-27, "fix(merge): restore src/compiler and src/lib to
origin for phase 1 bootstrap") removed the typed-facet implementation
(facet_static_registry, facet_resolution, facet_static_binding,
driver_facet_manifest_authority, facet_runtime, common.facet_abi...). The specs
were never removed. No open PR restores the feature.

This is not a HIR codec defect. Every example in the spec exercises the removed
feature, so none of them can run. The spec is tagged `@tag:in-development` so
the skip is counted and owned instead of reported as a 0-example run.

The same dead import is in:
- test/01_unit/compiler/semantics/facet_resolution_spec.spl
- test/01_unit/compiler/semantics/facet_acquire_expression_seal_guard_spec.spl

Resolution: restore the facet feature from the pre-fcbec1c3b62 tree (then drop
the tags), or delete all three specs.
