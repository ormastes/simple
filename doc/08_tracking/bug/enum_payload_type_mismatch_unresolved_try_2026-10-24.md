# enum_payload_type_mismatch_unresolved_try

Status: compiler fix committed (unverified: producer not rebuilt). Workaround tag may be removed once a producer with the fix is deployed.

Symptom: `enum construction 'BackendResult.Value': payload type mismatch at 0` (compiler.backend.interpreter process_module) for `val result = self.call_hir_function(f, [], ctx)?` then `BackendResult.Value(result)`.

Repro: test/fixtures/compiler/p3fix_mir/try (method in another module's `impl Host:`). Red on p2shard-6 stage2; the same shape without `?` is green.

Root cause: src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl lower_try_expr decoded the Ok payload only from enum_match_expr_type(base), which cannot find a method defined in another module's impl. The lowered call result already carried its declared Result (remember_call_hir_return); the payload stayed an untyped word, so the Let stored Infer and the payload check rejected it.

Fix: fall back to find_local_hir_type(res_local) for the Result type before decoding the Ok payload.
