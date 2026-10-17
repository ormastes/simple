# MIR return operand owner workaround (#3036)

Baseline: a9b5343d9dfbb9e6a38e074d7162092c58191b34.
Actual C36 mir_verify consumer: HIR95 PASS, MIR19 distinct errors.
Registered before edits: https://github.com/ormastes/simple/issues/3036.
Canonical key: mir_ret_optional_operand_owner_2026_10_11.

Seventeen ambiguity diagnostics group into four MirBlock return accessors:
bootstrap_ret_kind, bootstrap_ret_local_id, bootstrap_ret_const_kind, and
bootstrap_ret_const_scalar_text. Their unannotated `value ??
mir_operand_const_int(0)` loses the optional payload owner. `MirTerminator.Ret`
carries `MirOperand?`; `MirOperand.kind` is `MirOperandKind`, not `MirInstKind`.
Its Const payload belongs to `MirConstValue`. The extra empty runtime identity
and B5b multiple-wildcard errors may be cascades; only actual replay can show
whether they disappear with the owner restoration.

This patch explicitly imports terminal owners, declares the four coalesced
locals as MirOperand, and qualifies only those four methods' Ret/operand/constant
patterns. Original guards, fallbacks, Copy/Move distinction, output codes,
scalar formatting and aggregate zero-initializer values are preserved. The
StoreGlobal methods and producer lowering implementation are unchanged.
Four canonical workaround annotations map the exact methods to the OPEN bug.

The real MirBlock fixture exercises non-Ret, Ret(nil), Copy and Move with
different locals, all nine constant variants, both Bool values, lexical float
preservation, and aggregate formatting. It calls all four production accessors.
Native object and execution proofs remain pending independent source review
and manual owner replay; no full build is started here.

Retirement requires permanent producer optional/coalesce owner propagation and
an unannotated-source regression passing the same owner projections plus actual
mir_verify HIR/MIR/native qualification. Metadata registration is owned by the
object sweep lane; do not mark the bug solved from source inspection.
