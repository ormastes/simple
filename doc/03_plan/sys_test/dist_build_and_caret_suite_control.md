# Distributed build/Caret acceptance design

Date: 2026-10-12. Branch: `release_phase3`; inspected HEAD: `d5df0cb60`. Status: proposed planning/design, not implemented or runtime-qualified. This lane imports the supplied research without changing its historical claims. Existing uncommitted Caret production artifacts are preserved and remain separately owned. Scope is documentation; requirement selection precedes implementation.

Source acceptance scenarios AT-01–28 are retained verbatim in the [research](../../01_research/app/llm_caret/dist_build_and_caret_suite_control_research_plan_2026-10-11.md), section 18. Each feature in the [implementation plan](../app/llm_caret/dist_build_and_caret_suite_control.md) identifies its scenario range and exit evidence.

Implement scenarios using built-in matchers and independently supplied oracles, never self-comparison. Shared flow helpers proposed: step_enroll_host, step_open_remote_session, step_request_exact_environment, step_submit_build, step_validate_outputs, step_reconcile_attempt, step_reject_stale_receipt. Freeze signatures before delegation. Setup owns isolated fixtures; checkers compare retained typed receipts to expected identities. Missing provider/host/runtime is BLOCKED or NOT_RUN, never PASS.

Remote gates: AT-01–11,25–26; build gates: AT-12–20; CI/lifecycle: AT-21–24,27; RDMA: AT-28 only when enabled. Include deliberately wrong digest, stale generation, malicious link and forged receipt fixtures. Platform roles and native/emulated/container classes require independent evidence. No executable spec or generated PASS manual is authored until requirements are selected and real owner seams are bound.

## MDSOC++ checks

Add MD-01–07 from detail design: encapsulation, seal failure matrix, authority/budget rejection, bounded transfer, query purity/command identity, generation rollback and ECS/dynamic closure exclusions. Retain composition digest, generation, facet bindings, memory/concurrency policy and actual runtime receipt. No graph/source inspection substitutes for overload or crash-recovery execution.
