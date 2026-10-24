# enum_payload_type_mismatch_untyped_match_value

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: InferMode.Check payload mismatch and for-in over I64 in type_infer/inference_expr_calls.spl: 'val x = match k: case Function(_,_,e): e / case _: []' is untyped.

Workaround (tagged `@workaround bug=enum_payload_type_mismatch_untyped_match_value_2026-10-24`): explicit [Effect] and [HirType]? annotations, typed expected_param (src/compiler/30.types/type_infer/inference_expr_calls.spl).

Root fix location: match-expression result type unification in src/compiler/50.mir (join of variant-payload type and empty array literal / Some(..) with nil).
