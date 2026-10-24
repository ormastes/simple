# enum_payload_type_mismatch_untyped_match_value

Status: compiler fix committed (unverified: producer not rebuilt).

Symptom: InferMode.Check payload mismatch (type_infer/inference_expr_calls.spl) for `val effs = match k: case Function(_, _, e): e case _: []`.

Repro: test/fixtures/compiler/p3fix_mir/matchval. Red on p2shard-6.

Root cause: remember_merged_arm_identity required every arm typed; a context-free `[]` literal never is.

Fix: lower_array_lit marks context-free empty literals (empty_array_lit_locals); the join lets them adopt the other arms' type when it is an Array/Slice.

## Workaround record (phase-3 adhoc lane, landed with #4302)

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: InferMode.Check payload mismatch and for-in over I64 in type_infer/inference_expr_calls.spl: 'val x = match k: case Function(_,_,e): e / case _: []' is untyped.

Workaround (tagged `@workaround bug=enum_payload_type_mismatch_untyped_match_value_2026-10-24`): explicit [Effect] and [HirType]? annotations, typed expected_param (src/compiler/30.types/type_infer/inference_expr_calls.spl).

Root fix location: match-expression result type unification in src/compiler/50.mir (join of variant-payload type and empty array literal / Some(..) with nil).
