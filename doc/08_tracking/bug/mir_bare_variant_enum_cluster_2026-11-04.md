# MIR bare-variant / enum spec cluster (2026-11-04)

Seed `simple-ref`, one spec per run. RED: 5 specs failing.

## Fixed
1. Spec-stale: `bare_variant_retained_subject_spec`, `lambda_lift_if_enum_capture_scan_spec`
   asserted an empty error list, but a no-default enum match records the staged
   non-fatal diagnostic `non-exhaustive enum match on '...'`
   (`switch_operators_calls.spl` ~5182, `self.error`, since b2d42b02ecc 2026-08-01;
   warning now, error after phase 3). Both specs now filter exactly that text
   (precedent: `mir_option_result_qualified_field_spec.spl`).
2. Product bug (masked by 1): `lower_lambda_value_for_type` (same file, ~8169/8188,
   introduced by 770de8344fa "propagate fatal lifted-body errors") treated ANY
   child `lw.errors` entry as fatal, so a non-fatal warning in a lifted lambda
   body aborted the lift ("cannot materialize lambda for its declared function
   slot"). Now only `MirError.fatal` aborts; warnings propagate to the parent.

## Open (not fixed)
- `bare_variant_retained_subject_spec`: "retained owner does not declare bare arm"
  (shape check at ~4010 is guarded by `enum_match_expr_type(scrutinee) == nil`, but
  the expression is now typed, so the arm `Literal` is accepted as a KindA arm);
  and `case mut Leaf:` fails in the parser (`expected :, got Ident 'Leaf'`).
- `bare_variant_untyped_subject_reject_spec`: inner `match op: case Return` over a
  facade-imported payload binder emits a third `ematch_arm` (Return treated as a
  variant of Kind) and `undefined variable Return/Var` for the binding body.
- `bare_variant_unit_self_subject_spec`: expects 2/3 `ematch_arm` blocks for
  `case Null/case _` and `Int/Float/case _`; lowering emits 1/2 (one per enum arm,
  wildcard is the default). No B5b error. Spec arithmetic or a lost wildcard arm;
  needs a decision.
- `enum_subject_owner_recovery_spec`: "a present text or record fills a T? slot":
  `enum construction 'lib.data.CR.Success': payload type mismatch at 0`.

## Follow-up
- Lift now aborts on `mir_error_is_fatal` (flag or legacy-text allowlist, shared with
  the driver owner). `expr_dispatch.spl:625` ("cannot lower ... as a function value")
  emits a placeholder const 0 as a non-fatal error: promote it to `error_fatal`.
