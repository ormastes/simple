# Negative containment consumer fallback

Requirement: REQ-PHASE1-NEGATIVE-CONTAINMENT-CONSUMERS.
Bug: BUG-PHASE1-BDD-NEGATED-MATCHERS-20261011 remains OPEN.

Executable: test/01_unit/compiler/negated_matcher_consumer_predicate_spec.spl.
The control reads the unchanged direct grammar regression, requires nonempty real source, and asserts one present and one absent fragment. A distinct inversion probe rejects the false-to-true mutation (one failure, exit1).

Fourteen authorized consumer specs retain64negative predicates through contains(...).to_equal(false). Subjects, fragments, positive assertions, and direct grammar are unchanged.

Stage1 Windows bootstrap only; immutable producer15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb, pinned x86_64-pc-windows-msvc. No native/pure-Simple or JIT admission, zero rebuilds.

| Path | Exit | Authoritative example verdict |
| --- | --- | --- |
| test/01_unit/compiler/negated_matcher_consumer_predicate_spec.spl | 0 | OK declared>=1 executed=1 passed=1 failed=0 skipped=0 dropped=0 |
| test/01_unit/compiler/coverage_unary_not_conditions_spec.spl | 1 | ERROR declared>=4 executed=4 passed=0 failed=4 skipped=0 dropped=0 |
| test/01_unit/compiler/backend/llvm_codegen_adapter_trace_contract_spec.spl | 1 | ERROR declared>=3 executed=3 passed=0 failed=3 skipped=0 dropped=0 |
| test/01_unit/compiler/backend/llvm_object_path_target_lifetime_source_spec.spl | 1 | ERROR declared>=1 executed=1 passed=0 failed=1 skipped=0 dropped=0 |
| test/01_unit/compiler/backend/mir_text_codegen_signature_spec.spl | 1 | ERROR declared>=3 executed=3 passed=2 failed=1 skipped=0 dropped=0 |
| test/01_unit/compiler/mir/mir_trace_scope_contract_spec.spl | 1 | ERROR declared>=3 executed=3 passed=1 failed=2 skipped=0 dropped=0 |
| test/01_unit/compiler/tools/fix/rewriter_atomic_write_contract_spec.spl | 0 | OK declared>=2 executed=2 passed=2 failed=0 skipped=0 dropped=0 |
| test/01_unit/compiler/frontend/environment_variant_frontend_policy_binding_v1_spec.spl | 0 | OK declared>=6 executed=6 passed=6 failed=0 skipped=0 dropped=0 |
| test/01_unit/compiler/lint/lint_source_location_index_spec.spl | 0 | OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0 |
| test/01_unit/compiler/lint/perf_diagnostic_record_spec.spl | 1 | ERROR declared>=10 executed=10 passed=7 failed=3 skipped=0 dropped=0 |
| test/01_unit/compiler/lint/query_lint_ast_projection_contract_spec.spl | 1 | ERROR declared>=6 executed=6 passed=4 failed=2 skipped=0 dropped=0 |
| test/01_unit/compiler/lint/query_lint_closure_index_spec.spl | 1 | ERROR declared>=1 executed=1 passed=0 failed=1 skipped=0 dropped=0 |
| test/01_unit/compiler/lint/query_lint_last_statement_index_spec.spl | 0 | OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0 |
| test/01_unit/compiler/lint/query_lint_match_index_spec.spl | 0 | OK declared>=2 executed=2 passed=2 failed=0 skipped=0 dropped=0 |
| test/01_unit/compiler/lint/raw_sffi_call_spec.spl | 1 | ERROR declared>=18 executed=18 passed=17 failed=1 skipped=0 dropped=0 |

| test/01_unit/compiler/lint/raw_sffi_call_spec.spl | 1 | ERROR declared>=18 executed=18 passed=17 failed=1 skipped=0 dropped=0 |

Collection: one attempt per identity, no replay of passing checks. Source-contract and unresolved-owner failures remain OPEN, with exact logs retained under build/phase1-negated-matcher-20261011. Required pure-Simple verification cannot run because the release runtime is absent; draft remains necessary.

Final diagnostic aggregate: 66 executed, 48 passed, 18 failed; 6 passing files and 9 failing files. All15identities executed; zero skipped/dropped. These counts include the new predicatecontrol, not the separate expected-red grammar or inversion probes.

## Current source-owner corrections

Independent PR3023 merged at f3eb9e8a4c8a35f1de265062c3e804dd08a666f0.
Its five completed specs fix eight previously failing criteria: LLVM adapter3,
LLVM lifetime1, MIR signature1, AST projection2, closure lookup1. Criteria
were checked only after the relevant source-contract correction; all eight
passed, with six prior unchanged passes retained. No prior green was replayed.
MIR span ownership needed two bounded cycles; other changed criteria needed one.

This provides incremental coverage of the original66 examples:56 passing and
10 still failing. It is not a rerun of the original collection or a new native
qualification. The direct grammar and expected-red inversion evidence remain
unchanged. Source-contract status for the remaining four families is OPEN:

| Family | Remaining cases | Proven current owner issue | Concrete next repair/gate |
| --- | --- | --- | --- |
| Interpreter coverage | 4 | eval.spl eval_control_condition recursively composes and/or, but unary-not reaches generic eval_expr and records the enclosing expression. Expected bounded leaf counting and legacy/vector helpers are absent. | Repair unary-not operand traversal and qualify real AST condition receipts; decide bounded current-owner contract before replacing historical helper fragments. |
| MIR trace scope | 2 | module_lowering lower_module lacks trace_scope enter/exit; method-call/function trace gates lack the expected generation refresh although expr_dispatch has it. | Bind outer lowering to balanced trace scope and refresh persistent gates by actual generation, then qualify multiple lowering generations. |
| Performance diagnostics | 3 | lint_checks lacks lint_rule_code_from_easyfix_id and the claimed silent-default owner; its actual result filter still allocates filtered_results and uses should_keep_lint_result plus a separate level lookup. | Implement canonical malformed-safe code extraction; reconcile actual silent-default owner; replace duplicate filter policy with the existing lint_policy_decision and validate caller behavior. |
| Raw-SFFI snapshot | 1 | standalone snapshot behavior passes, but the Linter integration owner lacks the claimed raw_sffi_code_snapshot(content,path) combined traversal. | Wire one real snapshot into both ordered categories at the canonical lint owner and qualify call/declaration category ordering. |

These production integration/performance contracts are not repaired by assertion
weakening. Source/log identity receipts remain in residual-evidence.json and
original evidence.json. Missing pure-Simple runtime gates remain explicit.
