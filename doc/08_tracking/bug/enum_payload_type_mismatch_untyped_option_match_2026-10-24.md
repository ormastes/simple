# enum_payload_type_mismatch_untyped_option_match

Status: compiler fix committed for the `None` spelling (unverified: producer not rebuilt). The `nil` spelling stays rejected by design.

Symptom: HirExprKind.If/IfChain/Return/... payload mismatch (semantics.resolve resolve_expr) for `val x = match o: case Some(e): Some(f(e)) case nil: nil`.

Repro: test/fixtures/compiler/p3fix_mir/optmatch (uses `None`; red on p2shard-6). `val r = Some(f(b))` alone is green, so the Some arm is typed.

Root cause: remember_merged_optional_arm_type (mir_lowering_stmts.spl) accepts only a raw `nil` arm as the absence witness (and only in unsafe: nil is unsafe-only). A builtin `None` arm has no HIR type and bailed the join.

Fix: value-position `None` constructions are marked (option_none_locals) and join as the absence witness.

Source: resolve.spl's `case nil: nil` arms are a real source defect in safe code; spell them `None` (the annotation workaround widens nil in safe code).
