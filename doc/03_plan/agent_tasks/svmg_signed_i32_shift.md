# SVM-G checked signed i32 right shift

Claim: `01a1afac/pure-svmg-shift`. Branch: `work/pure-svmg-signed-shift-d88f`. The isolated baseline is `749d7855848d3695c74dda84f7e59ecab75abc78`, which contains the still-unmerged D4 repair. The running D4 diagnostic remains bound to that immutable input; this lane edits a separate worktree.

The existing Pure-Simple LLVM right-shift branch selects arithmetic shift for signed operands and logical shift for unsigned operands. SVM-G already provides distinct SAR and SHR opcodes. The defect is loss of checked left-operand signedness at the lowering selector, for both binary and compound right shifts.

Use `expr_is_signed_i32` to recognize only checked `Int(32, signed=true)`. Add a default-false third selector parameter, pass the binary left or assignment target classification, and select SAR only in the integer Shr arm. Preserve unsigned SHR, existing untyped fallback, float rejection and every other opcode. No mixed numeric promotion rule or new VM instruction is introduced. Selection stays constant time.

| Responsibility | Owner | Scope |
| --- | --- | --- |
| Production repair | mir_backlog_audit | `svmg_lowering.spl` only |
| Generated-bytecode execution regressions | mir_tag_abi_audit | Existing unit spec and separate ordinary driver |
| Integration, docs, verification and landing | root | Owned lane only |
| Independent final review | mir_p0_closure | Source and test evidence |

Shared interfaces: `expr_is_signed_i32`, third `is_signed: bool = false` parameter on both opcode selectors, `integer_shift_body`, and `expect_vm_shift_result`. Tests use real HIR, the production lowerer and actual reference VM. They must observe negative and positive signed results, zero/31/33 counts, compound assignment and unsigned high-bit controls. Float shifts remain rejected. Optional enum fields use the existing safe `None` contract.

No placeholder assertions, mock VM or source-string acceptance. Source review cannot replace execution or the required compiler/core/MCP checks. The parent D4 repair and this defect must both be verified and merged before either is represented as landed.

Status: implementation in progress; no executable or release PASS.
