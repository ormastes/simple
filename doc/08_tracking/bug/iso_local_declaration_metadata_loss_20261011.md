# Explicit local ISO declaration loses MIR transfer metadata

Status: source repair proposed; production admission and regressions BLOCKED.

At release a4ca8226e21f8df3374c3eea1109e6365c4d7d79, the two MIR Let
paths prefer initializer HIR metadata. The declaration fallback passes
isolation state zero to `remember_local_hir_type`. That owner normalizes the
explicit scalar argument: zero means missing/malformed, one means isolated,
two means non-isolated. It does not infer isolation from the supplied HIR type.
Later place-read transfer guards require state one to emit `Move`.
Therefore an explicit `val x: iso i64 = 5` can lose its transfer semantics
to ordinary initializer metadata. The parameter binder already computes the
correct scalar state from the declared type.

The proposed repair gives explicit isolated declarations precedence in both
Let metadata blocks, retaining their declared HIR type, scalar isolation state
one, and declared resource state. Non-isolated and unannotated fallback paths
are unchanged. This does not modify the NLL checker or fabricate use facts.
The original `iso_use_after_move_e2e_spec.spl` assertions remain unchanged.
New real-HIR regressions require the actual statement owner to preserve local
isolation state and emit a matching `Move`, with an exact non-iso `Copy` control.

Retained evidence reported two positive ISO failures and two negative-control
passes. No previous passing case was rerun. Three bounded changed-input
diagnostics used immutable cached bootstrap producer SHA256
15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb:

1. Two original failed end-to-end bodies: two executed, zero passed, two failed
   with `semantic: type mismatch: cannot convert enum to int`.
2. Two new actual-HIR statement regressions: two executed, zero passed, two
   failed with the same enum/integer error.
3. One instrumented focused regression: one executed, zero passed, one failed.
   `MirLowering.new` and `MirBuilder.begin_function` complete; the error occurs
   after the marker before `lower_stmt`, before the marker after it.

All three explicitly set SIMPLE_LIB to this isolated worktree's src tree.
That requested source root alone does not prove the cached producer resolved
every owner there: no successful statement-owner sentinel was reached. The
exact discriminant/enum ABI blocker remains unproven, and must be resolved in
an independent prerequisite scope before admission. No runtime PASS is claimed
for the repaired metadata, original e2e assertions, or native execution.

Receipts and terminal logs: build/phase1-iso-e2e-20261011/
current-imports.json, focused-owner.json, focused-stages.json. They pin producer,
entry, candidate owner and log hashes, source-root request and case selection.
Qualification is BOOTSTRAP_DIAGNOSTIC_ONLY; admitted is false. All children are
terminal, no rebuild or cache deletion occurred, and the three-cycle cap is
closed. Pure compiler/lib/MCP checks, runtime smokes and admitted e2e/MIR
regressions remain pending. Keep this production PR draft.
