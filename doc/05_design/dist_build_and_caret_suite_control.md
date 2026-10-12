# Distributed build and Caret Suite control: detail design

Date: 2026-10-12. Branch: `release_phase3`; inspected HEAD: `d5df0cb60`. Status: proposed planning/design, not implemented or runtime-qualified. This lane imports the supplied research without changing its historical claims. Existing uncommitted Caret production artifacts are preserved and remain separately owned. Scope is documentation; requirement selection precedes implementation.

Architecture: [ownership](../04_architecture/dist_build_and_caret_suite_control.md). Research: [integration record](../01_research/app/llm_caret/dist_build_and_caret_suite_control_research_plan_2026-10-11.md). Existing Caret product design remains authoritative for desktop/mobile, provider protocols and terminal rendering. This companion defines build integration and links overlapping work; it does not replace that product scope.

## Shared contracts and lifecycle

Extend existing contracts rather than creating parallel registries. SessionId and generation already exist in workbench/session_contract.spl; BuildHostV1, BuildTaskV1 and result validators exist in common/build_manager/contracts.spl; GatewayQuota and gateway_quota_admit exist in cache_gateway/quota.spl. New field names below are proposed, not discovered APIs.

ExecutionGrant: principal, issuer, project, host, operation set, environment constraint, budgets, policy revision, expiry, revocation epoch. EnvironmentBinding: actual host/runtime, compiler/toolchain digests, SDK/ABI/ISA, target, test runtime and isolation class. OperationEnvelope: version, operation ID, canonical payload digest, grant reference, session generation. ExecutionReceipt: exact source manifest, action/check selection, effective binding, outputs, execution times, cleanup, authority and signature.

Authenticate → validate schema → authorize → match environment → durably admit → reserve → execute existing owner → collect bounded outputs → parent validates → record terminal/cleanup receipt → publish. Exact duplicate operation returns retained outcome; changed payload under same ID is rejected. External write with lost acknowledgement is OutcomeUnknown. No automatic retransmission until owner evidence resolves it. Persist event and notification outbox atomically; replay uses monotonic revision and bounded retention.

## Feature algorithms, errors and boundaries

### F01 — Contracts and baseline

| Concern | Design |
|---|---|
| Invariant | Version, operation ID, payload digest, principal, policy revision and session generation are mandatory on new managed requests; a V1 decoder cannot discard V2 constraints. |
| Owner and algorithm | Boundary: `src/lib/common/build_manager/contracts.spl`. Algorithm/change: Inventory installed runtime digests and caller seams; add versioned authority/environment envelopes around existing V1 contracts; reject unknown required fields and preserve legacy fixtures. |
| Rejection evidence | Failure verification: AT-01–07; baseline and compatibility fixtures. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F02 — Host registry and credential roles

| Concern | Design |
|---|---|
| Invariant | Endpoint identity is pinned separately from SSH account, provider profile, node identity and signer identity; unknown enrollment never opens a connection. |
| Owner and algorithm | Boundary: `src/app/llm_caret`. Algorithm/change: Resolve independent host roles from strict SDN; enroll host fingerprint with explicit operator action; store credential references; implement rotation, revocation and dependency inspection. |
| Rejection evidence | Failure verification: AT-01,05,11,25; changed-key and revoked-role tests. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

F02 value boundary is `workbench/distributed_host_roles_v2.spl`. An authenticated enrollment/config owner must publish a bounded snapshot (maximum 128 hosts) with an exact registry revision, decoded SSH public-key SHA-256 digest in lowercase hex, and separate SSH-account/provider-profile/node/signer credential roles. Each role carries its own identity, secret reference, revision and revocation. Resolution validates all host identities and duplicate IDs before selecting; checks the observed host key and all selected roles; and never enrolls or opens a connection. Secret reference names are bounded to 256 bytes and reject traversal, whitespace and raw secret material. Reference resolution and secret access remain in the credential provider. Strict SDN loading, authenticated enrollment/rotation publication, dependency inspection and transport caller wiring are still required; the value resolver alone is not host authentication.

Strict configuration decoding is isolated in `workbench/distributed_host_registry_sdn_v2.spl`: schema `distributed-host-registry-v2`, positive registry revision and hosts array; each host requires exactly host_id, host_key_digest and the four named role records; each role requires exactly identity, credential_reference, revision and boolean revoked. Unknown/missing fields, scalar coercions, duplicate keys/IDs and wrong versions fail. Input is bounded to 64 KiB and 128 hosts. The shared untrusted parser runs first for structural limits, followed by its issue-aware parser to reject last-wins duplicate handling. This bounded second parse is justified only on configuration publication; the owner must retain the decoded snapshot and never parse per request. Decoding preserves revoked records; admission rejects their use. Authenticated configuration publication, enrollment and rotation transactions are still required.

### F03 — Scoped grants and approvals

| Concern | Design |
|---|---|
| Invariant | Approval resolves once against authenticated approver, request digest, policy revision, expiry and generation. Provider CLI shell activity remains contained by host controls. |
| Owner and algorithm | Boundary: `src/app/llm_caret/tools.spl`. Algorithm/change: Pass immutable caller context into permission_decision; enforce project/host/operation/resource scopes at remote admission; bind approval to exact digest; add safe filesystem owner integration and actual account sandbox. |
| Rejection evidence | Failure verification: AT-03–06,11,26; forged approval, path-race and bypass rejection. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F04 — Managed SSH and persistent sessions

| Concern | Design |
|---|---|
| Invariant | smux owns PTY/VT; client EOF detaches; input and size leases are distinct. Timeout yields ownership unknown, never PID-only adoption or duplicate launch. |
| Owner and algorithm | Boundary: `src/app/llm_caret/workbench/session_contract.spl`. Algorithm/change: Extend SessionId generation binding with host boot/service/process identities; invoke a fixed broker with framed typed stdin; launch provider through existing execution/smux owners; persist session bindings and reconcile reconnect. |
| Rejection evidence | Failure verification: AT-01,02,07–10,19; real remote turn, detach and reconnect receipt. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F05 — Caret controls and model tools

| Concern | Design |
|---|---|
| Invariant | Read-only preview never takes terminal geometry lease. Session close, turn cancel, build cancel and history delete require separate verbs and scopes. |
| Owner and algorithm | Boundary: `src/app/llm_caret/tools.spl`. Algorithm/change: Add host/project/environment selectors to existing cs workbench; keep provider grammar; expose typed inspect, submit, status, cancel and artifact tools; capture target generation before queuing input. |
| Rejection evidence | Failure verification: AT-03,07–10,12; tui captures and stale-target rejection. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F06 — Exact environment matching

| Concern | Design |
|---|---|
| Invariant | Session host, execution host, compilation target and test runtime are separate fields. ENV_NO_MATCH reports failed predicates; no local or emulated fallback. |
| Owner and algorithm | Boundary: `src/lib/common/build_manager/contracts.spl`. Algorithm/change: Define requested profile versus observed binding; probe runtime/compiler/SDK/ABI/ISA/isolation; filter eligible authorized workers before reservation; worker revalidates effective binding. |
| Rejection evidence | Failure verification: AT-12–14,27; native-versus-emulated mismatch fixtures. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F07 — Immutable snapshots and build execution

| Concern | Design |
|---|---|
| Invariant | Admitted→Reserved→Running→Collecting→Settled; disconnect enters OwnershipUnknown. Retry waits for prior terminal/reap evidence; cleanup cannot touch agent worktree. |
| Owner and algorithm | Boundary: `src/app/bootstrap_builder/transport.spl`. Algorithm/change: Capture files and links consistently with digest manifest; stage through typed broker; retain existing DAG/retry owner; allocate exclusive attempt root and resource lease; parent admits only declared validated outputs. |
| Rejection evidence | Failure verification: AT-13,15,19,20; two-host build and failure/cancel/reap receipts. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

Execution-provider implementation dependency: the existing `builder_worker_memory_admit_v1` in `src/app/bootstrap_builder/worker.spl` rejects every positive enforced-memory request, publishes a no-child-started receipt and settles capacity as no-parent-owned. Its process-observation request uses zero enforced bytes and `None`; this worker therefore cannot satisfy distributed enforced-memory admission. The build capsule must select a separately qualified cgroup/Job worker through its host facet before accepting dispatch. Provider qualification must demonstrate the actual per-tree memory limit, descendant containment, cancel/reap evidence and retained cleanup uncertainty. Do not reinterpret monitor-only execution as enforcement or treat a provider rejection as successful execution. The journal execution claim is only the durable authority boundary; it supplies no enforcement by itself. Implementation and real provider verification remain open.

### F08 — Shared CAS, quotas and grouped compiler state

| Concern | Design |
|---|---|
| Invariant | Digest integrity is independent of publication authorization. Group-shared indexes are read-only and compiler/source/toolchain qualified. Exhaustion falls back only where optional cache semantics allow. |
| Owner and algorithm | Boundary: `src/app/cache_gateway/quota.spl`. Algorithm/change: Add authorized namespace lookups; atomically reserve temporary and committed bytes; pin active inputs; single-flight immutable fetch; journal reservations and release; connect compiler keys without sharing writable attempt state. |
| Rejection evidence | Failure verification: AT-16–18; concurrent quota, corruption and pin tests. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F09 — Native Windows and platform host facades

| Concern | Design |
|---|---|
| Invariant | App logic stays common; host differences stay in SOSIX/provider leaves. JobObject, WSL, Hyper-V and process-isolated container are different runtime classes. |
| Owner and algorithm | Boundary: `src/app/bootstrap_builder/windows_group_broker.spl`. Algorithm/change: Reuse Windows broker/process port and ConPTY owners; implement typed filesystem and process calls through host facades; qualify both connection directions and paths with spaces/non-ASCII. |
| Rejection evidence | Failure verification: AT-02,06,08,14,20,27; actual windows installed-binary receipts. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F10 — Signed evidence and GitHub CI

| Concern | Design |
|---|---|
| Invariant | Bind receipt to source/head/base candidate, test selection, environment, policy, artifacts, signer and expiry. Developer assertions cannot satisfy trusted-executor checks. |
| Owner and algorithm | Boundary: `src/app/ci/pipeline_runner.spl`. Algorithm/change: Submit common Jobs from CI; encode check-specific receipts; isolate executor attestation and protected verifier keys; extend base-owned pr-fast-check verifier; report every required check on all selected events. |
| Rejection evidence | Failure verification: AT-05,21,22,25; forged/stale receipt and fork-event fixtures. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F11 — SHS/SDN containers and images

| Concern | Design |
|---|---|
| Invariant | Canonical equivalent plans have equal digest; meaningful runtime differences change binding. Native-container demand fails if only weaker class is available. |
| Owner and algorithm | Boundary: `src/app/ci/pipeline_runner.spl`. Algorithm/change: Normalize SHS authoring and direct SDN to one validated plan; bind interpreter and provider overlays; qualify native runtime providers; pin image generation per attempt; drain before replacement. |
| Rejection evidence | Failure verification: AT-13,23,27; equivalent recipe and real provider receipts. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F12 — Source updates and disposable attempts

| Concern | Design |
|---|---|
| Invariant | Updating a branch never mutates an admitted attempt; restart only discards settled attempt storage. User edits remain in separate worktree ownership. |
| Owner and algorithm | Boundary: `src/app/bootstrap_builder/transport.spl`. Algorithm/change: Resolve new revision to new snapshot; allocate fresh scratch; retain active source/image pins; reconcile process/artifact ownership before GC; add rollback generation and session-edit preservation. |
| Rejection evidence | Failure verification: AT-15,19,20,23; update-during-build and rollback fixture. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F13 — Inbound mirror and guarded backup

| Concern | Design |
|---|---|
| Invariant | Fetch failure reports stale data; mirror cannot push canonical refs implicitly. Snapshot uses pinned object IDs, never latest alias. |
| Owner and algorithm | Boundary: `scripts/scv-migration/push-both.shs`. Algorithm/change: Keep outbound backup separate; add inbound bare-mirror controller with ref allowlist; resolve commits, gitlinks and LFS objects to snapshot manifest; expose fetch age and conflict; recover failed atomic publication. |
| Rejection evidence | Failure verification: AT-23,24; divergence, failed fetch and wrong gitlink tests. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F14 — Additional hosts and opportunistic clients

| Concern | Design |
|---|---|
| Invariant | Capability discovery is not execution proof. Offline client ownership must reconcile before retry; unsupported role stays UNSUPPORTED. |
| Owner and algorithm | Boundary: `src/lib/common/build_manager/contracts.spl`. Algorithm/change: Admit enrolled client workers with explicit budgets and runtime classes; qualify macOS/FreeBSD/SimpleOS and ARM/RISC-V separately; bind cross-target and native/emulated test identities. |
| Rejection evidence | Failure verification: AT-12,14,19,20,27; per-role installed native/emulated receipts. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F15 — Qualified TLS and optional RDMA

| Concern | Design |
|---|---|
| Invariant | SSH vertical slice remains independent. RDMA is not HTTPS; outstanding work drains and revoked buffer generations invalidate before memory reuse. |
| Owner and algorithm | Boundary: `src/app/bootstrap_builder/transport.spl`. Algorithm/change: Introduce qualified secure RPC provider behind existing operation contracts; parity-test auth/replay/cancel; later add RDMA artifact path with bounded grants and completion retirement. |
| Rejection evidence | Failure verification: AT-11,28; transport parity and hardware retirement receipts. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |

### F16 — Operational evidence and performance

| Concern | Design |
|---|---|
| Invariant | No source inspection becomes runtime PASS. Publish sample counts and p50/p95/p99 where justified; proposed numerical budgets require baseline and user selection. |
| Owner and algorithm | Boundary: `doc/03_plan/sys_test`. Algorithm/change: Retain fixture/runtime/host digests and raw timing/RSS; measure cold/warm startup, input responsiveness, build/CAS states and reconciliation independently; add diagnostic redaction, drain, revoke and rollback procedures. |
| Rejection evidence | Failure verification: AT-01–28; failure-injection matrix and measured baseline. Return structured rejection before side effects for bad schema, grant or environment. After side effects, retain ownership/cleanup uncertainty rather than reporting clean success. |


## MDSOC++ capsule interaction design

The [architecture](../04_architecture/dist_build_and_caret_suite_control.md) defines layers, visibility matrix, adapter paths and facet graph. The product composition layer performs resolution/lifecycle/routing only; Session, Build, Artifact, EvidenceCI and SourceLifecycle keep their own domain state. Proposed shared envelopes live in common/contracts/distributed_control_v2.spl; no cross-capsule mutable handles enter payloads.

| Concern | Detailed design and rejection behavior |
|---|---|
| Identity | Use common.kernel_plugin KpfId128/KpfDigest256 and existing MDSOC++ descriptors. Facet IDs, major/minor versions and capacity units freeze in M1 before consumers. No copied identity registry in Caret or CI. Actual sealer: mdsocpp_seal_v1(capsules: [CapsuleDescriptorV1], policy: MdsocppSealPolicyV1) -> MdsocppSealResultV1. |
| Commands | Proposed submit_build(OperationEnvelope, BuildRequestV2) returns AdmissionResultV2; sender transfers an immutable value; Build is sole attempt mutator. Receiver checks caller, grant, generation and digest again. Cancellation targets that same authority and exact attempt. |
| Queries | Proposed query_build(BuildIdentityV2, CallerContextV2) returns bounded BuildViewV2; enforce read scope; no domain mutation or implicit environment refresh. Views include observed revision and truthful unknown status. |
| Events | BuildEventV2 carries generation, attempt ID, revision, kind and digest-bound value. Progress coalesces by attempt; terminal outcomes, approval resolutions and settlement cannot be dropped or coalesced away. Durable replay cursor precedes reclamation. |
| Capacity | Proposed initial policy: 256 command slots/capsule, 64 KiB command frame, 1 MiB query page, 1024 event slots and 64 MiB transient routing budget. These are baseline candidates requiring user/NFR selection, not measured limits. Full queues reject admission with typed Overloaded; never unbounded buffering. Artifact bytes stream separately under byte reservations. |
| Scheduling | Use `src/lib/nogc_async_mut_noalloc/kernel_plugin/fixed_runtime.spl` as the bounded runtime foundation for routing; extend through its facade only; per-owner hot calls stay direct. Fair bounded drains prevent output flood starving revocation/cancel. A response deadline does not release ownership or infer remote death. |
| Transfer | Capsule-internal storage may be GC-managed; no-GC routing holds copied/serialized bounded values or owned immutable descriptors, never borrowed mutable objects crossing async lifetime. Sender/receiver lifetimes are explicit. |
| Feedback | Static required-facet graph is acyclic. Completion events return via subscription/outbox with a queue bound and cursor; they create no reciprocal required implementation import. |
| Activation | Prepare descriptor set and compatibility fixtures; seal against authority/budget; allocate new generation without effects; drain or explicitly fence existing work; migrate private state; atomically commit activation receipt. In-flight work remains pinned until owner settlement. |
| Recovery | Crash before activation keeps old generation; after commit recover exact new receipt. No partial registry publication. Migration failure retains previous schema/data or documented restore path; retire generation only after all borrowed resources/grants are invalidated. |
| Isolation | Composition permission is not OS confinement. HostAuthority grants narrowly scoped capabilities; signer stays in protected provider; host filesystem/process owners independently enforce bounds. Runtime-open vendor adapters remain outside static critical proof. |
| ECS | Initial uses_ecs=false; future arrays/ECS are internal to a capsule, never domain object sharing. Kernel and drivers retain MDSOC-only policy. |

## MDSOC++ acceptance supplement

| ID | Requirement | Negative oracle / evidence | Owner milestone |
|---|---|---|---|
| MD-01 | Shared contracts and tree-private capsule internals | Import graph fixture rejects sibling-private access and duplicated shared schema | M1 / F01 |
| MD-02 | Sealed required/provided facet resolution | Missing/duplicate/ambiguous facet and dependency cycle rejected by sealer | M1 / F01 |
| MD-03 | Capability and capacity admission | Denied bits, memory overflow and concurrency overflow rejected before side effects | M1 / F03 |
| MD-04 | Bounded immutable transport | Oversized frames/full queue rejected; mutable references cannot cross capsule boundary | M2–M4 / F04,07,08 |
| MD-05 | One command authority/read-only queries | Concurrent duplicate command mutates once; repeated query leaves domain revision unchanged | M3 / F07 |
| MD-06 | Generation migration and rollback | Crash on either side of activation commit; failed migration and outstanding-call drain preserve correct generation | M7 / F12 |
| MD-07 | Honest ECS/runtime-open boundary | Kernel/Driver ECS profile rejected; dynamic critical closure rejected; vendor capability stays separately qualified | M8 / F14,15 |

The architecture/model inspection proves foundation availability only. MD-01–07 execution is NOT_RUN. Future SPipe specs must retain actual sealer/runtime receipts and independent oracles alongside AT-01–28; no source-text presence check may establish runtime PASS.

<!-- sdn-diagram:id=dbc.design -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbc.design hash=sha256:auto render=ascii
@layout dag
@direction LR
Client -> Admission
Admission -> SealCheck
SealCheck -> BuildCommand
BuildCommand -> ResourceReservation
ResourceReservation -> ExistingWorker
ExistingWorker -> ParentAdmission
ParentAdmission -> ReceiptOutbox
ReceiptOutbox -> ClientView
```

</details>
<details class="sdn-ascii" open>
<summary>Diagram — authored preview, generation NOT_RUN</summary>

```ascii generated-from=dbc.design hash=sha256:auto
Client -> Admission -> SealCheck -> BuildCommand -> ResourceReservation
 -> ExistingWorker -> ParentAdmission -> ReceiptOutbox -> ClientView
```

</details>
<!-- sdn-diagram:end -->
