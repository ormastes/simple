# Distributed build and Caret Suite control: implementation plan

Date: 2026-10-12. Branch: `release_phase3`; inspected HEAD: `d5df0cb60`. Status: proposed planning/design, not implemented or runtime-qualified. This lane imports the supplied research without changing its historical claims. Existing uncommitted Caret production artifacts are preserved and remain separately owned. Scope is documentation; requirement selection precedes implementation.

Research: [source](../../../01_research/app/llm_caret/dist_build_and_caret_suite_control_research_plan_2026-10-11.md). Companion: [detail design](../../../05_design/dist_build_and_caret_suite_control.md). Existing uncommitted Caret product plan: `doc/03_plan/app/llm_caret/caret_suite_production.md` (separate owner; not included in this PR). DBC milestones here and CSP milestones there are separate namespaces. Shared work must have one owner and one acceptance receipt.

## Delivery sequence

M0 baseline → M1 contracts → M2 SSH session → M3 exact remote build → M4 bounded CAS → M5 Windows → M6 trusted CI → M7 lifecycle → M8 additional platforms/transports. First integrated topology: Caret A → provider session B → exact-environment build C → parent-admitted artifacts A. Two physical hosts are acceptable if service roles are reported.

## Feature implementation work packages

### F01 — Contracts and baseline

Milestone: M0–M1. Requirements: DBC-001, DBC-018, DBC-022, DBC-023. Owner anchor: `src/lib/common/build_manager/contracts.spl`. Estimate: 3–5 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Inventory installed runtime digests and caller seams; add versioned authority/environment envelopes around existing V1 contracts; reject unknown required fields and preserve legacy fixtures.

Exit: Baseline and compatibility fixtures; acceptance AT-01–07. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F02 — Host registry and credential roles

Milestone: M1. Requirements: DBC-003, DBC-005, DBC-019, DBC-020. Owner anchor: `src/app/llm_caret`. Estimate: 4–6 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Resolve independent host roles from strict SDN; enroll host fingerprint with explicit operator action; store credential references; implement rotation, revocation and dependency inspection.

Exit: Changed-key and revoked-role tests; acceptance AT-01,05,11,25. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F03 — Scoped grants and approvals

Milestone: M1. Requirements: DBC-001, DBC-006, DBC-019, DBC-020. Owner anchor: `src/app/llm_caret/tools.spl`. Estimate: 5–8 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Pass immutable caller context into permission_decision; enforce project/host/operation/resource scopes at remote admission; bind approval to exact digest; add safe filesystem owner integration and actual account sandbox.

Exit: Forged approval, path-race and bypass rejection; acceptance AT-03–06,11,26. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F04 — Managed SSH and persistent sessions

Milestone: M2. Requirements: DBC-003, DBC-004, DBC-017, DBC-021, DBC-024. Owner anchor: `src/app/llm_caret/workbench/session_contract.spl`. Estimate: 6–10 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Extend SessionId generation binding with host boot/service/process identities; invoke a fixed broker with framed typed stdin; launch provider through existing execution/smux owners; persist session bindings and reconcile reconnect.

Exit: Real remote turn, detach and reconnect receipt; acceptance AT-01,02,07–10,19. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F05 — Caret controls and model tools

Milestone: M2–M3. Requirements: DBC-001, DBC-002, DBC-004, DBC-017. Owner anchor: `src/app/llm_caret/tools.spl`. Estimate: 4–6 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Add host/project/environment selectors to existing cs workbench; keep provider grammar; expose typed inspect, submit, status, cancel and artifact tools; capture target generation before queuing input.

Exit: TUI captures and stale-target rejection; acceptance AT-03,07–10,12. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F06 — Exact environment matching

Milestone: M3. Requirements: DBC-002, DBC-003, DBC-007, DBC-015. Owner anchor: `src/lib/common/build_manager/contracts.spl`. Estimate: 4–7 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Define requested profile versus observed binding; probe runtime/compiler/SDK/ABI/ISA/isolation; filter eligible authorized workers before reservation; worker revalidates effective binding.

Exit: Native-versus-emulated mismatch fixtures; acceptance AT-12–14,27. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F07 — Immutable snapshots and build execution

Milestone: M3. Requirements: DBC-007, DBC-008, DBC-009, DBC-014, DBC-021. Owner anchor: `src/app/bootstrap_builder/transport.spl`. Estimate: 6–10 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Capture files and links consistently with digest manifest; stage through typed broker; retain existing DAG/retry owner; allocate exclusive attempt root and resource lease; parent admits only declared validated outputs.

Exit: Two-host build and failure/cancel/reap receipts; acceptance AT-13,15,19,20. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F08 — Shared CAS, quotas and grouped compiler state

Milestone: M4. Requirements: DBC-010, DBC-016. Owner anchor: `src/app/cache_gateway/quota.spl`. Estimate: 5–8 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Add authorized namespace lookups; atomically reserve temporary and committed bytes; pin active inputs; single-flight immutable fetch; journal reservations and release; connect compiler keys without sharing writable attempt state.

Exit: Concurrent quota, corruption and pin tests; acceptance AT-16–18. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F09 — Native Windows and platform host facades

Milestone: M5. Requirements: DBC-009, DBC-011, DBC-015, DBC-023. Owner anchor: `src/app/bootstrap_builder/windows_group_broker.spl`. Estimate: 6–10 days plus host availability, excluding unavailable infrastructure. Status: OPEN.

Implementation: Reuse Windows broker/process port and ConPTY owners; implement typed filesystem and process calls through host facades; qualify both connection directions and paths with spaces/non-ASCII.

Exit: Actual Windows installed-binary receipts; acceptance AT-02,06,08,14,20,27. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F10 — Signed evidence and GitHub CI

Milestone: M6. Requirements: DBC-005, DBC-013, DBC-019, DBC-022. Owner anchor: `src/app/ci/pipeline_runner.spl`. Estimate: 5–8 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Submit common Jobs from CI; encode check-specific receipts; isolate executor attestation and protected verifier keys; extend base-owned pr-fast-check verifier; report every required check on all selected events.

Exit: Forged/stale receipt and fork-event fixtures; acceptance AT-05,21,22,25. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F11 — SHS/SDN containers and images

Milestone: M7. Requirements: DBC-011, DBC-012, DBC-018, DBC-023. Owner anchor: `src/app/ci/pipeline_runner.spl`. Estimate: 5–9 days plus provider availability, excluding unavailable infrastructure. Status: OPEN.

Implementation: Normalize SHS authoring and direct SDN to one validated plan; bind interpreter and provider overlays; qualify native runtime providers; pin image generation per attempt; drain before replacement.

Exit: Equivalent recipe and real provider receipts; acceptance AT-13,23,27. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F12 — Source updates and disposable attempts

Milestone: M7. Requirements: DBC-007, DBC-009, DBC-014, DBC-021. Owner anchor: `src/app/bootstrap_builder/transport.spl`. Estimate: 3–5 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Resolve new revision to new snapshot; allocate fresh scratch; retain active source/image pins; reconcile process/artifact ownership before GC; add rollback generation and session-edit preservation.

Exit: Update-during-build and rollback fixture; acceptance AT-15,19,20,23. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F13 — Inbound mirror and guarded backup

Milestone: M7. Requirements: DBC-007, DBC-014. Owner anchor: `scripts/scv-migration/push-both.shs`. Estimate: 3–5 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Keep outbound backup separate; add inbound bare-mirror controller with ref allowlist; resolve commits, gitlinks and LFS objects to snapshot manifest; expose fetch age and conflict; recover failed atomic publication.

Exit: Divergence, failed fetch and wrong gitlink tests; acceptance AT-23,24. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F14 — Additional hosts and opportunistic clients

Milestone: M8. Requirements: DBC-002, DBC-003, DBC-009, DBC-015, DBC-022. Owner anchor: `src/lib/common/build_manager/contracts.spl`. Estimate: Per profile: 4–8 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Admit enrolled client workers with explicit budgets and runtime classes; qualify macOS/FreeBSD/SimpleOS and ARM/RISC-V separately; bind cross-target and native/emulated test identities.

Exit: Per-role installed native/emulated receipts; acceptance AT-12,14,19,20,27. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F15 — Qualified TLS and optional RDMA

Milestone: M8. Requirements: DBC-005, DBC-018, DBC-020, DBC-024. Owner anchor: `src/app/bootstrap_builder/transport.spl`. Estimate: TLS 5–10; RDMA 10–20 days, excluding unavailable infrastructure. Status: OPEN.

Implementation: Introduce qualified secure RPC provider behind existing operation contracts; parity-test auth/replay/cancel; later add RDMA artifact path with bounded grants and completion retirement.

Exit: Transport parity and hardware retirement receipts; acceptance AT-11,28. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

### F16 — Operational evidence and performance

Milestone: M0–M8. Requirements: DBC-015, DBC-016, DBC-022. Owner anchor: `doc/03_plan/sys_test`. Estimate: 3–5 days plus soak, excluding unavailable infrastructure. Status: OPEN.

Implementation: Retain fixture/runtime/host digests and raw timing/RSS; measure cold/warm startup, input responsiveness, build/CAS states and reconciliation independently; add diagnostic redaction, drain, revoke and rollback procedures.

Exit: Failure-injection matrix and measured baseline; acceptance AT-01–28. Dependencies: preceding milestone contracts; freeze compatibility fixture before downstream use. Submit one owner-scoped implementation PR with negative tests, guide/expert updates and retained execution evidence.

## Verification and completion

Map every DBC-001–024 and AT-01–28 before implementation. Each milestone must record actual runtime digest, source revision, host identity, evidence level, fixture, command, exit status and cleanup. Run each acceptance once after its final change; at most three repair cycles. Static design validation does not qualify any runtime feature. Baseline-first numerical NFR selection is OPEN.

Implementation gates include core/lib/MCP checks and native smokes whenever changed dependencies require them, direct-env facade audits, SSpec source-to-manual traceability and zero executable specs under doc/06_spec. Future executable acceptance scenarios belong under test/03_system/app/llm_caret/feature; generated manuals mirror that path. No placeholder PASS scenarios are created by this documentation lane.

## Rollout and rollback

Feature-flag V2 managed requests while legacy V1 users retain honest compatibility behavior. Enable only qualified host/runtime cohorts. Drain attempts before changing service/image generations. Retain old schema/binary and backup receipt until restore is demonstrated; incompatible required constraints fail closed. Publication and privileged host enrollment require separately authorized operator action.

## Decisions before implementation

The supplied research proposes the complete scope. User selection of final feature requirements and measured NFR budgets remains necessary. This document details all proposals without selecting optional capabilities. Defer no feature silently: M8 retains explicit TLS/RDMA and other-host work.

## MDSOC++ implementation gates

M1 must freeze facet IDs, shared envelope schemas and descriptors, then bind existing common.kernel_plugin and lib/mdsocpp sealer/runtime rather than creating another kernel. M2–M4 must use bounded immutable command/query/event transport with one domain authority. M7 must demonstrate generation activation, migration and rollback; M8 must preserve static proof exclusions. MD-01–07 in the detail design supplement AT-01–28 and are required before implementation qualification. Buffer budgets are proposed baseline candidates, pending NFR selection.
