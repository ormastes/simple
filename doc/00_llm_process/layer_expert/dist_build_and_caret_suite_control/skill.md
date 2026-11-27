# Distributed build and Caret integration knowledge

Proposal only. Canonical decisions and feature ownership are in [detail design](../../../05_design/dist_build_and_caret_suite_control.md) and [implementation plan](../../../03_plan/app/llm_caret/dist_build_and_caret_suite_control.md). Extend existing session/build/Job/cache owners; never infer native or trusted CI qualification from static documents. All runtime work remains OPEN until selected requirements and actual host receipts exist.

## Shared orchestration endpoints (2026-11-15)

Simple, Orchestrator, Caret and agents share named server contexts or select
independent consumer mappings. See the [setup guide](../../../07_guide/tooling/orchestration_server_contexts.md),
[host identity guide](../../../07_guide/tooling/orchestration_host_identity.md),
[architecture](../../../04_architecture/server_contexts.md), and
[test plan](../../../03_plan/sys_test/server_contexts.md).

Use the common pure selection contract and existing controller/execution
owners. Endpoint metadata does not authorize trusted CI, provision a host,
change Caret's listener or prove container reachability. The source and
[manual](../../../06_spec/01_unit/lib/common/config_core/server_context_v1_spec.md)
remain AWAITING_VERIFICATION/NOT_RUN until admitted runtime and real host
receipts exist; this crosslink does not close the distributed-build proposal.
