# Distributed build/Caret acceptance design

Date: 2026-10-12. Target branch: `release_phase3`. Initial design inspected HEAD `d5df0cb60`; full F01–F16 scope was subsequently selected by the user. Status: implementation in progress, runtime/provider acceptance incomplete. This lane retains the supplied research without changing its historical claims. Existing uncommitted Caret production artifacts remain separately owned. See the implementation progress ledger for source and producer-bound evidence.

Source acceptance scenarios AT-01–28 are retained verbatim in the [research](../../01_research/app/llm_caret/dist_build_and_caret_suite_control_research_plan_2026-10-11.md), section 18. Each feature in the [implementation plan](../app/llm_caret/dist_build_and_caret_suite_control.md) identifies its scenario range and exit evidence.

Implement scenarios using built-in matchers and independently supplied oracles, never self-comparison. Shared flow helpers proposed: step_enroll_host, step_open_remote_session, step_request_exact_environment, step_submit_build, step_validate_outputs, step_reconcile_attempt, step_reject_stale_receipt. Freeze signatures before delegation. Setup owns isolated fixtures; checkers compare retained typed receipts to expected identities. Missing provider/host/runtime is BLOCKED or NOT_RUN, never PASS.

Remote gates: AT-01–11,25–26; build gates: AT-12–20; CI/lifecycle: AT-21–24,27; RDMA: AT-28 only when enabled. Include deliberately wrong digest, stale generation, malicious link and forged receipt fixtures. Platform roles and native/emulated/container classes require independent evidence. Requirements are selected. Executable system scenarios still require real owner seams; generated manuals must retain actual execution status and may not claim PASS from authored source or unit fixtures.

## MDSOC++ checks

Add MD-01–07 from detail design: encapsulation, seal failure matrix, authority/budget rejection, bounded transfer, query purity/command identity, generation rollback and ECS/dynamic closure exclusions. Retain composition digest, generation, facet bindings, memory/concurrency policy and actual runtime receipt. No graph/source inspection substitutes for overload or crash-recovery execution.

## Current F02 source regression trace

| Requirements / acceptance | Source scenarios | Evidence scope |
|---|---|---|
| DBC-003 / AT-01,05 | `distributed_host_roles_v2_spec.spl`: unknown enrollment, changed key, stale registry, duplicate identity | Pure value resolution; NOT_RUN |
| DBC-005,020 / AT-11,25 | Separate SSH/provider/node/signer roles, independent revocation, shared-reference dependency inspection and stale inspection rejection | Pure role/dependency values; NOT_RUN |
| DBC-018 / AT-01,05 | `distributed_host_registry_sdn_v2_spec.spl`: exact schema and nested roles, duplicate top/nested keys, closed fields/types, retained revocation, size/capacity limits | Actual SDN source decoding; NOT_RUN |

These files reside under `test/01_unit/app/llm_caret/`. They do not replace the remote system gates. Next F02 acceptance must exercise authenticated configuration publication, explicit enrollment and changed-key rejection before connection; rotate/revoke role credentials through their real owner; and prove a stale snapshot cannot open a new session or disclose operation state. An unavailable provider remains BLOCKED/NOT_RUN. Preserve revoked dependencies in rotation inspection and require an exact revision when publishing the replacement snapshot.

## Runtime qualification prerequisite

The c27cb117… producer rebuilt compiler modules and passed bootstrap sanity/receiver checks, but its compiler matrix is still pending and the independent native callback execution regression failed. General CLI/test/SPipe use remains unqualified. A successful compile/link is insufficient: text-returning callback and captured record-returning array-loop behavior must be correct. The scoped callback retry limit is exhausted; retain and report the failure rather than repeating its test. Full acceptance coverage, coverage measurement and generated execution manuals remain incomplete.

## Current F04 source regression trace

`test/01_unit/app/llm_caret/distributed_session_binding_v2_spec.spl` traces DBC-017/020/021 and AT-07–10/19: exact boot/service/generation/ticket identity, separate action scopes, input/geometry lease independence, monotonic expiry and detach preserving process/turn state. All scenarios are NOT_RUN and pure metadata checks. Real acceptance still requires the fixed broker and authoritative process/smux leases, EOF/reconnect behavior, no PID adoption, independent turn/job cancellation and terminal/ownership-unknown receipts.
