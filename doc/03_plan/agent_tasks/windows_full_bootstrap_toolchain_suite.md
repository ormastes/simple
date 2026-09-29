<!-- codex-design -->
# Windows Full Bootstrap and Toolchain Suite Agent Tasks

## Frozen Shared Surface

- Interfaces: `BootstrapPhaseReceipt`, `ToolPrimaryFeatureReceipt`, `SuiteAcceptanceRow`, `DeploymentRollbackReceipt`.
- Flow steps: `Admit the phase compiler and provenance`; `Check compiler and interpreter behavior`; `Run essential tools in interpreter and native modes`; `Verify integrated tool suites`; `Review and publish the exact phase head`; `Deploy and prove rollback`; `step_bootstrap_platform_handoff_readiness`.
- Helpers: `setup_windows_bootstrap_phase`, `check_phase_provenance`, `check_phase_compiler_interpreter`, `check_phase_tool_matrix`, `check_integrated_suite_matrix`, `check_local_deploy_and_rollback`.
- Unimplemented helpers fail with `fail(...)` or `assert(false)` and cannot emit PASS.

## Lanes

1. Compiler/interpreter/bootstrap lineage: conflict resolution, frozen source, Stage 1/2, typed Stage 3/4 admission, exact phase checks.
2. CLI/MCP/LSP/SPipe/DevHub/Caret: interpreter/native tool evidence, protocol requests, cache invalidation, performance/RSS.
3. IDE/T32/platform/deployment: production entry behavior, provider classification, generation transaction, rollback, readiness rows.

Lower-model sidecars may gather bounded evidence and propose changes. Merge owner is `/root`. Final exact-head review, phase admission, generated-manual acceptance, broad exclusion, publication, and done marks belong to the highest-capability primary reviewer.

## Ordered Merge Plan

1. Resolve existing conflicts without absorbing unrelated work.
2. Implement/shared-review receipt and attempt-ledger gaps only where existing owners are insufficient.
3. Wire the RED system spec to production evidence helpers.
4. Run Phase 1/Stage 2 build and its complete phase matrix.
5. Review/publish Stage 2, then repeat for Stage 3 and Stage 4.
6. Run integrated suites, deploy/rollback, docs/manual refresh, and final verification.

