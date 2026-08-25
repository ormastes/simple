# MDSOC cross_query cannot construct `CrossDimensionResult` — missing construct_types import

**Date:** 2026-08-25  **Status:** FIXED 2026-08-25 (see Resolution)  **Severity:** medium (whole cross-dimension query API is unusable)

## Symptom
`bin/simple test test/01_unit/compiler/mdsoc/gpu_layer_facets_spec.spl` (Rust seed, interpreter engine):

```
✗ lists exactly the three GPU facet files in 70.backend
    semantic: function `CrossDimensionResult` not found
Results: 9 total, 8 passed, 1 failed
```

## Root cause
- `src/compiler/85.mdsoc/cross_query.spl:11` — the only import is `use compiler.mdsoc.types.*`.
- `src/compiler/85.mdsoc/types/__init__.spl` exports zero construct-dimension symbols (`grep -c construct` = 0).
- `src/compiler/85.mdsoc/cross_query.spl:60` builds `CrossDimensionResult(matching_files: ..., ...)`, and
  the signatures at `:18-22`, `:66-69`, `:75-78` name `ConstructCapsule`, `CrossDimensionQuery`,
  `CrossDimensionResult`. All three live in `compiler.mdsoc.construct_types`
  (`src/compiler/85.mdsoc/construct_types.spl:3-8`), which is never imported.
- Same pattern in `src/compiler/85.mdsoc/construct_checker.spl:10` — `check_capsule_deps` (`:109`),
  `check_shared_consistency` (`:125`) and `register_capsules` (`:164`) take `ConstructCapsule` /
  `SharedBinding` with no `construct_types` import. Not yet exercised by a live spec.

This is why `test/01_unit/compiler/mdsoc/cross_query_spec.spl` and `construct_checker_spec.spl`
sit as `it "skipped"` scaffolds ("functions/imports not available").

## Reproducing spec
`test/01_unit/compiler/mdsoc/gpu_layer_facets_spec.spl` — `describe "cross_query over gpu_backend facets"`
(kept RED per `.claude/rules/testing.md`; the other 8 examples in the file are green).

## Unblock condition
Add `use compiler.mdsoc.construct_types.{ConstructCapsule, CrossDimensionQuery, CrossDimensionResult}`
to `cross_query.spl` (and `{ConstructCapsule, SharedBinding}` to `construct_checker.spl`), then
un-skip `cross_query_spec.spl` / `construct_checker_spec.spl`. Out of scope for the GPU-test lane
that found it (edit scope was limited to `config.spl`).

## Resolution (2026-08-25, same day)
FIXED: `src/compiler/85.mdsoc/cross_query.spl` now imports `ConstructCapsule`, `CrossDimensionQuery`,
`CrossDimensionResult` from `compiler.mdsoc.construct_types.*`. Evidence (Rust seed, interpreter):
`test/01_unit/compiler/mdsoc/gpu_layer_facets_spec.spl` -> `Results: 9 total, 9 passed, 0 failed`
(the cross_query case is the reproduce; the other 8 are the neighbours); `cross_query_spec.spl` -> `1 passed`.
Still latent, NOT fixed here: `construct_checker.spl:10` has the same import shape for
`check_capsule_deps`/`check_shared_consistency`/`register_capsules` — no spec exercises them yet.
