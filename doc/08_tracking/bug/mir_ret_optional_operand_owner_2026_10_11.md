# Optional return operand coalescing loses MIR owner

OPEN; GitHub https://github.com/ormastes/simple/issues/3036. Actual C36 mir_verify on source a9b5343d9dfbb9e6a38e074d7162092c58191b34 has HIR95 PASS then MIR19 errors in graph return accessors: four coalesced MirOperand optional locals lose owner; enum patterns belong to MirOperandKind and MirConstValue.

Reviewed source workaround 35112626d670a52393a6d6e0f62a206ce03326d6 adds explicit MirOperand locals and qualified patterns with four canonical source markers. Native HIR/MIR/object replay and runtime fixture remain PENDING. No global optional/coalesce repair or bootstrap qualification claimed.

Workaround: https://github.com/ormastes/simple/commit/35112626d670a52393a6d6e0f62a206ce03326d6; recovery parent `a9b5343d9dfbb9e6a38e074d7162092c58191b34`. Release landing not established.

Producer: `5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235`. Evidence: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-sdn-frontend/mir-verify/error-groups.json`.

Reproducing/prevention fixture: `test/fixtures/compiler/mir_ret_operand_owner/main.spl`. Four canonical `@workaround` markers already exist in the reviewed source commit; this registration does not change production code.

Removal condition: Permanent optional/coalesce owner propagation repair plus original unannotated source regression and actual mir_verify HIR/MIR/native object PASS, with return-operand runtime controls. Keep OPEN while workaround active; no automatic retirement or admission.
