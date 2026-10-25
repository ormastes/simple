# HIR validation blob encoded per module, then decoded and mostly refused

- **Status:** Fixed
- **Date:** 2026-10-25
- **Area:** compiler / 80.driver (retained HIR loop, post-HIR RT-criticality validation)

## Symptom
Stage-3 bootstrap of the `bootstrap_main` closure (1442-1453 modules, Windows stage2 native):
- Per-module segment `hir-post-store -> next hir-file-start` averaged **292 ms** (421 s total,
  memory-snapshot attempt 780574, 1442 modules); the validation blob encode dominated it.
- Post-loop `phase3:hir:validate:rt_criticality:start -> done` took **78 s**.
- In `s3-bis-new`, **1237 of 1453 blobs (85%) were refused** (`[hir-blob-refused] RT-E-HIR-BLOB-DECODE`)
  and validation proceeded on the in-memory fallback array.

## Mechanism
`lower_and_check_retained_owner_impl` (`driver_hir_pipeline_lowering.spl`) called
`hir_module_encode_retained_v1` for every module and pushed it to `ctx.validation_module_blobs`.
The only consumer, `validate_rt_criticality_diagnostics_blobs` (`rt_criticality_validation.spl`),
decoded each blob again and, on any codec refusal, validated `validation_module_array` instead.
The fallback array is therefore already the authoritative transport; the encode+decode is wasted.
The closure needs RT policy only when a criticality claim exists or a module has `@rt`/HAL.

## Fix
- Blob encode is off by default; `SIMPLE_HIR_VALIDATION_BLOBS=1` re-enables it
  (`driver_hir_validation_blob_encode_enabled_v1`). With no blobs the validator routes to the
  array variant (existing empty-blobs contract).
- The scalar facts `validation_module_has_rt_hal` / `validation_module_claim_counts` are now
  pushed for every retained module (previously only for modules whose blob encoded).
- `driver_rt_criticality_errors` short-circuits via `driver_rt_criticality_policy_needed_v1`:
  when the flags cover every module, no claim exists and no module has `@rt`/HAL, it calls
  `rt_bound_manifest_clear()` and returns `[]` without decoding or walking bodies. If the flags
  do not cover every module (streaming lane, dict fallback), the full validator runs as before.

## Pin
`test/01_unit/compiler/driver/driver_hir_validation_blob_policy_spec.spl`
(mirror: `test/unit/compiler/driver/`).

## Expected effect
About -420 s of HIR loop time and -78 s post-loop on the 1442-module closure.
