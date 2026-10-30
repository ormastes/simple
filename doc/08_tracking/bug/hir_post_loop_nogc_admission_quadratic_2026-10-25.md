# HIR post-loop NOGC param-effect admission was quadratic

- **Status:** Fixed
- **Date:** 2026-10-25
- **Area:** compiler / 80.driver (phase3 HIR validate, ownership admission)

## Symptom
Stage-3 bootstrap of the 1442-module `bootstrap_main` closure spent **198 s**
between `phase3:hir:validate:start` and
`phase3:hir:validate:value_struct_layouts:start` (attempt 780574). The only
work in that gap is `driver_admit_nogc_param_effects_v1(self.ctx,
surfaces.surfaces)` (`driver_hir_pipeline_lowering.spl`).

## Mechanism (n = 1442)
All in `src/compiler/80.driver/driver_hir_pipeline_support.spl`:
1. `driver_nogc_param_effect_admission_round_v1` (~l.342): a full scan of
   `surfaces` per module to find matching `canonical_path` -> O(n x surfaces).
2. `driver_nogc_param_effect_admission_v1` (~l.441): per round,
   `for actual in pending: for checked in receipt.modules` -> O(pending x admitted).
3. `driver_admit_nogc_param_effects_v1` (~l.468): `for actual in
   admission.modules: for key in modules.keys()` with a HirModule copy per
   probe -> O(n^2).
(The selection sort over canonical paths was already replaced by
`hir_admission_path_order_v1`, commit 7db42fe70fa.)

## Fix
New pure helpers in `src/compiler/80.driver/hir_admission_order_v1.spl`:
`hir_admission_identity_key_v1` (name + "\n" + path),
`hir_admission_unadmitted_indices_v1` (Dict membership), and
`hir_admission_group_positions_v1` (key -> ordered positions). Surfaces are
indexed by canonical path once per round (matching surfaces still visited in
original order, so `conflicting` is unchanged); round membership uses a Dict;
write-back maps identity -> all alias dict keys once. Output order,
diagnostics and `bootstrap_entry_hir` handling are unchanged.

## Pin
`test/01_unit/compiler/driver/driver_nogc_param_effect_admission_linear_spec.spl`
(+ mirror under `test/unit/compiler/driver/`).

## Expected effect
198 s -> well under 1 s; the whole gap is this call.
