# HIR frontend diagnostics: Any-alias message and cross-module inferred fallback (2026-10-30)

Status: open
Area: compiler/35.semantics/lint/hir_frontend_diagnostics.spl

## Symptom

- `test/01_unit/compiler/lint/frontend_diag/any_warn_rules_acceptance_spec.spl`, example "flags an
  unannotated alias of an Any value": exactly one W-HIR-INFER-003 is emitted, but its message lacks
  "it is initialised from `b`". The alias branch at `hir_frontend_diagnostics.spl:687` is not taken
  for `val c = b` when `b` is an `Any` parameter.
- `test/01_unit/compiler/lint/frontend_diag/inferred_type_fallback_use_spec.spl`:
  - two examples fail with `array index out of bounds: index is 0 but length is 0` (imported fn
    returning a third-module struct)
  - "still fires when only the facade FUNCTION is imported..." finds 0 instead of 1

## Root cause

Not isolated. The parameter-symbol registration in `any_syms` does not seem to cover `Any`
parameters, and the cross-module return-type fallback path finds no findings and indexes an empty
list. Both need a debugging pass on the HIR diagnostics walker.

## Unblock

Fix the walker. Then remove the `pending` markers that link here.
