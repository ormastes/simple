# enum_payload_type_mismatch_untyped_match_value

Status: compiler fix committed (unverified: producer not rebuilt).

Symptom: InferMode.Check payload mismatch (type_infer/inference_expr_calls.spl) for `val effs = match k: case Function(_, _, e): e case _: []`.

Repro: test/fixtures/compiler/p3fix_mir/matchval. Red on p2shard-6.

Root cause: remember_merged_arm_identity required every arm typed; a context-free `[]` literal never is.

Fix: lower_array_lit marks context-free empty literals (empty_array_lit_locals); the join lets them adopt the other arms' type when it is an Array/Slice.
