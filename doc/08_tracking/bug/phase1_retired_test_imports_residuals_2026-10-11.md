# Retired test imports: unresolved contract slice

Status: DRAFT. Imports repaired; actual residual failures block completion.

The twelve specs below now import std.spec instead of the nonexistent std.test.
All executable assertions and fixture bodies remain unchanged. Full collection
across seventeen specs executes90, passes60, fails30; five independent complete
passes land separately. This slice contains73executed,43passed,30failed.

| Spec | Executed | Failed | First recorded diagnostic |
|---|---:|---:|---|
| test/01_unit/compiler/backend/actor_runtime_abi_contract_spec.spl | 1 | 1 | expected # Legacy actor-hook compatibility surface. |
| test/01_unit/compiler/semantics/rt_criticality_spec.spl | 26 | 5 | semantic: function rt_profile_assurance_rank not found |
| test/01_unit/os/kernel/arch/x86_32_user_page_root_owner_v1_static_spec.spl | 10 | 1 | expected -1 to be greater than 0 |
| test/01_unit/os/kernel/loader/authenticated_fs_exec_async_source_contract_spec.spl | 3 | 3 | expected """Authenticated filesystem-exec submission adapter. |
| test/01_unit/os/kernel/loader/authenticated_fs_exec_remote_submission_v1_static_spec.spl | 4 | 1 | expected """Authenticated filesystem-exec submission adapter. |
| test/01_unit/os/kernel/loader/riscv32_sv32_tcb_transfer_owner_v1_static_spec.spl | 2 | 2 | semantic: undefined field: unknown property or method 'not' on String |
| test/01_unit/os/kernel/loader/x86_32_mapping_tcb_transfer_owner_v1_static_spec.spl | 7 | 2 | semantic: undefined field: unknown property or method 'not' on String |
| test/01_unit/os/kernel/scheduler/scheduler_arm32_mapping_handle_v1_static_spec.spl | 4 | 3 | semantic: undefined field: unknown property or method 'not' on String |
| test/01_unit/os/kernel/scheduler/scheduler_current_execution_snapshot_v1_static_spec.spl | 3 | 1 | semantic: undefined field: unknown property or method 'not' on String |
| test/01_unit/os/kernel/scheduler/scheduler_riscv32_mapping_handle_v1_static_spec.spl | 3 | 3 | semantic: undefined field: unknown property or method 'not' on String |
| test/01_unit/os/kernel/scheduler/x86_32_mapping_handle_v1_static_spec.spl | 6 | 4 | semantic: undefined field: unknown property or method 'not' on String |
| test/03_system/compiler/bootstrap_centralized_storage_roots_spec.spl | 4 | 4 | semantic: in call to read_text (declared at line 789): function expects 1 argument(s), but 2 were provided (set SIMPLE_DEBUG_FIELD_ACCESS=1 for the calling fr |

Evidence: build/phase1-test-imports-20261011/CLOSURE_SUMMARY.json, selected.json,
and per-case exact source/log/producer hash receipts. Bootstrap producer15102d
clears import prerequisites but does not qualify current imported implementation
closure, pure-runtime/native/compiler/MCP gates, or the full4758row backlog.
No compiler rebuild, green rerun, or weakened assertion. Keep this slice draft
until real residual contract failures are investigated and resolved.
