# Complete the SVM-G D4 deferred subset

The existing design section 4.4 and bug `svmg_d4_lowering_deferred_subset_2026-08-07` require both integer printing and float compound arithmetic. Completing only one does not close the bug.

Source baseline: `9e39c485948e048933c6115785b36209be11b1af`. Isolated branch: `work/pure-svmg-d4-d88f`. Claim: `01a1afac/pure-svmg-d4`.

| Responsibility | Owner | Files |
| --- | --- | --- |
| Production lowering of both gaps | mir_backlog_audit | `src/compiler/70.backend/svmg_lowering.spl` |
| Actual HIR-to-bytecode-to-reference-VM regressions | mir_tag_abi_audit | `test/01_unit/compiler/backend/svmg_lowering_spec.spl` |
| Bounded verification-route investigation | mir_priority_fixes | Private evidence only |
| Contract, integration, merge | root | This plan and bug report |
| Independent final source review | mir_p0_closure | Private evidence only |

Shared production interfaces: `lower_print_int(arg: HirExpr)` and `assign_opcode(op: HirAssignOp, is_float: bool = false)`. Preserve the existing `compound_assign` emission path. Shared test helper names, when needed: `run_print_body`, `float_compound_body`, `expect_vm_print_log`. Assertions must observe actual generated-bytecode execution; no placeholder passes.

Acceptance requires decimal output for zero, signed boundaries, computed/local values, repeated calls and single evaluation; checked unsigned-width behavior must be explicit. Float addition, subtraction, multiplication and division must execute with float opcodes and preserve integer behavior. Float remainder, bitwise operations and shifts remain unsupported. Existing literal-string output and unsupported-type diagnostics remain covered.

Source review and static guards cannot establish execution acceptance. A source-matched self-hosted run and the required compiler/core/MCP checks remain necessary before landing. Any ordinary diagnostic must use the actual changed lowerer and actual reference VM, retain source/producer/runtime identities and stay within recorded resource limits. Do not retry unchanged failures or reopen capped foundation work.

Status: implementation in progress; no verification PASS or merge claimed.
