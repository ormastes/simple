# Simple Caret distributed execution

## Full feature, architecture, shared-daemon refactoring, and implementation plan

**Date:** 2026-11-06, Asia/Seoul  
**Revision:** 1.0 — proposed implementation plan, not a deployed protocol version  
**Repository:** ormastes/simple  
**Source-inspection baseline:** release/1.0.0 at `3ef23d69caa361369603a761f114c5613f7ea7b7`  
**Scope:** Caret suite, smux, Simple Orchestrator, its host daemon, Simple Container, and shared build/test execution infrastructure.

This is a source-grounded design and implementation plan. No repository implementation, deployment, daemon startup, or live container qualification was performed for this report. “Present” below means inspected source exists, not that the integrated system has passed runtime tests. Official platform documentation was rechecked on 2026-11-06; platform capabilities must still be qualified against the installed versions.

This document extends the earlier `simple_iac_orchestrator_unified_sdn_2026-11-04.md` into a standalone implementation plan. It preserves the single-SDN-format decision and corrects two implementation-status ambiguities: Linux container lifecycle is already wired into a CI execution path, whereas a canonical live Windows provider was still described as proposed at the inspected revision. Existing Docker wrappers are not proof of a qualified Windows provider.

## 1. Decisions and direct answers

1. **Reuse and harden the existing shared infrastructure.** There is already a daemon SDK, owned service lifecycle, exact process ownership, build/test task journal, and a general distributed-operation V2 journal. Do not create a second daemon framework, duplicate journal implementation, or competing writer for the same domain. Independent domain owners still need independent journals.
2. **Simple Container is a local execution library/provider layer, not the host daemon and not the cluster scheduler.** It may retain a standalone CLI. The host daemon composes its providers; the orchestrator decides global placement.
3. **Share mechanisms, not all application state.** Build/test runners, cache daemon, host daemon, and smux need common lifecycle, transport, journals, and supervision primitives. They must not become one privileged process with one mutable database.
4. **Keep one terminal authority.** smux owns the logical terminal session, attachment leases, input/geometry authority, and output replay. The container provider owns its native exec/attach transport; the host daemon coordinates lifecycle, without creating a second PTY reader or competing process supervisor.
5. **Use existing orchestration contracts and SDN parsing.** Extend strict typed resource dispatch and schemas. Do not introduce another YAML parser, a new shell DSL, or separate IaC and orchestration syntax.
6. **First delivery:** qualify and extend the existing Linux OCI path with Podman as the explicit first backend. In parallel, remove unsafe legacy wrapper behavior. Then implement and qualify the canonical Windows Docker process-isolation provider.
7. **Existing Kubernetes can be used.** It is an optional execution/control-plane backend, not something this design prohibits. For a Kubernetes-managed pool, Kubernetes owns node placement and runtime resources. Native Simple-managed pools use the Simple host daemon. Never let both account for and launch the same host resources independently.
8. **Apple container and FreeBSD jail fit through explicit adapters.** Apple container runs Linux VMs on macOS, not native macOS processes. FreeBSD jail is a native FreeBSD lane. Neither should be mislabeled as a Linux rootless Podman host.
9. **Lower CPU/memory allocations may improve admission only within declared minima.** They cannot turn one exclusively assigned physical GPU into several independent GPUs. GPU sharing requires an explicit, supported sharing mode.
10. **Do not promise exactly-once arbitrary commands.** Use immutable operation identities, fencing, retained outcomes, and reconciliation. A lost response or host heartbeat is uncertainty, not proof that an agent stopped.

### Terminology

“IaC” means infrastructure-as-code/configuration in this report, including the user's earlier “ioc” wording. Literal IoC/dependency-injection configuration is a different concern: retain the existing DI configuration semantics. If DI resources later share the same envelope, give them a distinct kind and authority; do not silently reinterpret `config/di.sdn`.

A **workload** is an admitted execution request; an **attempt** is one fenced execution incarnation; a **session** is a stable user-facing terminal/conversation identity. A session can survive a client disconnect without implying that its process can survive a host reboot.

## 2. What already exists and what remains

The repository links in Appendix A are pinned to the inspected revision.

| Area | Inspected evidence | Reuse | Missing or unsafe part |
| --- | --- | --- | --- |
| Strict orchestration SDN | `resource_v1.spl`, `ci_v1.spl` [S01–S02] | Pod/Deployment; Job/Pipeline; typed quantities, strict errors and source spans | Unified nested resource dispatch; host/resource profiles; interactive workload schema; richer placement and GPU claims |
| Container common contract | `container/runtime_v1.spl` [S03] | Exact runtime identity, intents and operation/result envelopes | Portable trait is probe-only; do not assume a complete common lifecycle interface |
| Linux OCI execution | `providers/linux/oci_runtime_v1.spl` [S04] | Prepare, create, start, inspect, wait, logs, stop, destroy and recovery | Workspace/env/secret/exec/TTY/device integration; stats currently unavailable; real-host conformance |
| Actual CI container wiring | `app/ci/pipeline_runner.spl` [S05] | Real Linux lifecycle calls and recovery-aware cleanup receipts | Current inspected path is synchronous and single-container; distributed interactive execution is additional work |
| Build/container admission | `container_worker_admission.spl` [S06] | Pure checks joining build action/attempt/node, toolchain, immutable input and fences | Does not itself launch or attest remote execution |
| Windows | Architecture and legacy Docker/test wrappers [S07, S08] | Compatibility policy and existing operational knowledge | Canonical Windows provider was proposed; Docker-first engine choice must explicitly update the older containerd/runhcs design |
| Daemon SDK | `nogc_sync_mut/daemon_sdk/` [S09–S10] | Existing daemon lifecycle, clients and request processing | Serial handler loop despite “max_concurrent”; ignored response-write failure followed by request deletion; PID-based recovery |
| Owned services/processes | `service/daemon_base.spl`, `io/group_process_owner.spl` [S11–S12] | Owned start/stop; exact-generation start/recover/cancel/reap | Consistent adoption across consumers; remote authorization and container-specific evidence |
| Build/test shared journal | `common/task_runner/contracts.spl`, `journal.spl` [S13–S14] | Writer lock, nonce lease, registered inventory, commit-before-projection, process/evidence identities | V1 kinds are build/test only; do not silently widen them for agents |
| General operation journal | `distributed_operation_journal_v2.spl` and distributed contracts [S15–S17] | Fenced ownership, immutable operation identity, retained outcomes, execution recovery to outcome-unknown | Explicit durability profiles, checkpoint/compaction and long-lived host integration |
| Local task scheduler | `fiber_scheduler.spl` [S18] | Bounded local work scheduling and existing build/test reuse | Its intentional memory-overcommit-for-progress rule is not safe host/container quota admission |
| Test daemon | CLI, light daemon, generic SDK daemon [S19–S21] | Existing entrypoints, test-specific warm state and cleanup policies | Two paths need convergence; inspected light loop is serial and uses Linux-specific liveness |
| Build runner/cache | Build entrypoint/database session and cache-daemon entrypoint [S22–S24] | Shared task infrastructure and parent-owned result/cache publication | Build CLI is not evidence of a single shared running build/test daemon; remote evidence is explicitly rejected today |
| smux/CoreMux | Typed port, execution contracts, owner and client [S25–S29] | Persistent owner, typed launches, attachments, leases, receipt reconciliation | Framed owner route/production composition remain incomplete; client configuration is loopback-only |
| Caret | Pane/runtime/workspace/session files [S30–S35] | Session binding V2; distinct control actions and input/geometry leases | Direct smux, independent process and tmux routes diverge; hardcoded provider/generation; incomplete provider-specific CLI adapters |

Important status distinction: the existing design documents, typed contracts, descriptors, authored tests, runtime wiring, and qualified deployment are separate evidence levels. The mux wire design listed 28 authored cases as `NOT_RUN`; this report does not convert those into passing tests.

## 3. Ownership and component boundaries

### 3.1 Architecture

~~~mermaid
flowchart TD
    C["Caret / CLI / MCP"] --> O["Simple Orchestrator"]
    B["Build / test parent owners"] --> O
    O --> H["Host daemon"]
    O --> K["Optional Kubernetes adapter"]
    H --> R["Simple Container providers"]
    H --> M["smux owner"]
    C --> M
    R --> X["Owned workload / exec stream"]
    M --> X
    H --> D["Shared daemon / journal / process libraries"]
    B --> D
    M --> D
~~~

The Caret-to-smux connection is authenticated or tunneled; it is not a public plaintext connection. The two edges to a workload represent different authority: the provider controls runtime execution, while smux exclusively controls the attached terminal stream and logical terminal state. The optional Kubernetes lane needs a qualified terminal-owner placement/adapter of its own.

| Component | Owns | Must not own |
| --- | --- | --- |
| Caret suite | User intent, provider choice, task/conversation UI, attachment client, approval presentation | Global scheduling, runtime handles, unrestricted host engine access |
| Simple Orchestrator | Desired resources, template resolution, admission, global placement, tenant quota, assignment fences and accepted status | PTY/native handles, provider-specific shell commands, build semantic result acceptance |
| Host daemon | Authenticated host registration, local resource ledger, assignment execution, local recovery, provider composition, owned cleanup inventory | Cluster-wide policy as a second scheduler; build DAG or test semantics |
| Simple Container | Runtime probing, image and mount policy, create/exec/stop/destroy, native identity, enforcement and execution evidence | Global queues, enrollment, interactive UI, resource-profile preference scoring |
| smux | Session identity, one terminal reader, terminal state/replay, attachments, input/resize leases and terminal control | Host selection, GPU allocation, arbitrary container destruction |
| Build/test parent | DAG readiness, affected-test selection, warm/reset rules, accepted verdicts and output/cache publication | Independent creation of an already-orchestrated attempt |
| Shared daemon/runtime libraries | Lifecycle, transports, timers, bounded work dispatch, journals, ownership, cancellation/reaping primitives | A universal mutable domain model or implicit elevation |
| Optional privileged broker | Narrow authorized operations that genuinely require privilege | Arbitrary runtime socket forwarding, general shell execution on behalf of a caller |

### 3.2 Deployment composition

- A host may run one orchestration service per machine or per permitted user scope. Advertise that scope in its identity; do not merge two rootless users' runtime stores.
- Register `physicalHostId` separately from `serviceScopeId`. Multiple user-scoped daemons still share physical CPU, RAM and GPUs: require one machine-wide capacity authority or explicitly disjoint delegated budgets/device sets. Normalize physical GPU identity across scopes; two private runtime stores do not create two physical GPUs.
- Per-workspace test services and per-user cache services remain separate owners, but use the same improved libraries.
- smux may remain an independent service so a host control connection restart does not automatically kill terminal sessions.
- Administrative provisioning is separate from normal workload operation. Linux rootless service, Windows service/broker, launchd and FreeBSD rc.d adapters have different privilege requirements.
- A local-only workflow must still work without an orchestrator. In managed pools, local launches must use the same host admission authority or an explicitly partitioned unmanaged budget.
- A control-plane process restart and a host reboot have different consequences. Neither may silently adopt a PID from stored metadata.

## 4. Feature inventory and priority

P0 is required before remote mutation or migration of existing users. P1 completes the first usable distributed Caret workflow. P2 expands platforms and operational capability.

| ID | Priority | Required feature | Observable completion criterion |
| --- | --- | --- | --- |
| CFG-01 | P0 | One strict SDN resource load/dispatch path | IaC-only, orchestration-only and combined fixtures decode without reparsing child values |
| CFG-02 | P0 | Versioned schema and canonical plan | Duplicate/unknown fields, unresolved references and changed-plan apply are rejected with spans |
| DAE-01 | P0 | Safe request/response commit ordering | Response-write failure never discards an unacknowledged request |
| DAE-02 | P0 | Exact-instance daemon ownership | Hung ping, PID reuse and stale lease cannot kill/adopt an unrelated process |
| DAE-03 | P0 | Reusable operation journal | Lost reply and restart reconcile one immutable operation; changed payload is rejected |
| DAE-04 | P1 | Event-driven bounded execution | Long workload does not block health, cancellation or other ready work |
| DAE-05 | P1 | Journal durability/compaction | Selected durability is real; restart after checkpoint/compaction preserves outcome and dedupe |
| HOST-01 | P0 | Authenticated enrollment and capability report | Configuration cannot falsely grant privilege, runtime or GPU capability |
| HOST-02 | P0 | Strict local admission and resource ledger | Concurrent grants cannot reserve the same exclusive device or exceed a hard budget |
| HOST-03 | P1 | Reconcile, drain and recovery | Host restart inventories only exact-owned resources and reports unknown state honestly |
| ORCH-01 | P1 | Placement and resource profiles | Hard minima stay hard; effective allocations and queue reasons are visible |
| ORCH-02 | P0 | Fenced assignment and result acceptance | Delayed old host/result cannot regain authority after a new generation |
| ORCH-03 | P1 | Fair queue, quotas and scarce-resource policy | CPU-only work does not unnecessarily block GPU work; waiting tasks do not starve |
| CTR-01 | P1 | Podman execution/stream feature completion | Real workspace-backed agent starts, streams, resizes, exits and cleans exactly |
| CTR-02 | P0 | Exact cleanup and typed argv | No runtime-global prune or name-only kill; quoting and command override tests pass |
| CTR-03 | P1 | Windows Docker process provider | Correct host/image pair, actual process mode, exact IDs, limits and cleanup qualified |
| MUX-01 | P1 | Complete typed owner/client composition | Local and remote clients use CoreMux; duplicate create does not duplicate execution |
| MUX-02 | P0 | Separate control authorities | Detach, cancel turn, cancel job, terminate and delete history are not conflated |
| CARET-01 | P1 | IaC-backed session creation | User requests a template/task, sees placement, and attaches to the selected agent CLI |
| CARET-02 | P1 | Provider-specific agent adapters | Each supported CLI has independently tested launch, auth and resume semantics |
| RUN-01 | P1 | Shared build/test execution adapter | Domain result/reset/publication rules stay with their parent owners |
| RUN-02 | P1 | Verified remote evidence | Parent validates immutable input/toolchain/attempt/output evidence before acceptance |
| OPS-01 | P1 | Explain, inspect, logs, retention and audit | One correlation chain follows resource to attempt, runtime, smux and result |
| EXT-01 | P2 | FreeBSD, Apple and Kubernetes adapters | Each advertises only its tested execution OS, isolation and feature set |

## 5. Shared daemon refactoring

### 5.1 Reuse map: do not start over

Use the following existing layers in combination:

1. `daemon_sdk`: public compatibility entrypoints, request service lifecycle and shared client behavior.
2. `daemon_base_start_owned` / `daemon_base_stop_owned`: retain and pass the updated ownership values, not older by-value convenience wrappers.
3. `group_process_owner`: native process broker and exact-generation cancel/recover/reap.
4. Task-runner journal: keep build/test attempt inventory and parent result ownership.
5. Distributed-control V2 plus distributed-operation journal: generic remote command identity, admission, retained outcomes and uncertainty.
6. Existing sosix I/O/process/clock and typed mux ports: platform effects remain in their appropriate leaves.

The `nogc_async_mut/daemon_sdk` compatibility facade is not evidence that underlying request handling is nonblocking. Implement actual asynchronous waiting/dispatch before advertising that property.

### 5.2 Fix the current SDK before reusing it remotely

| Current behavior | Required change |
| --- | --- |
| Synchronous handler loop limited by `max_concurrent` | Preserve legacy semantics as documented batch count; introduce versioned `maxInFlight` and bounded asynchronous workers rather than silently changing V1 |
| Response-write result ignored before request removal | Claim request, persist admitted operation, persist executing/intent before an effect, perform/reconcile, persist terminal outcome, atomically publish response, then acknowledge/remove request |
| File disappearance used as completion | Result/outcome record is authoritative; missing request/response is not proof of nonexecution |
| Failed ping can trigger PID-based kill | Distinguish unreachable, unhealthy, stopping and dead; require exact owner/process identity and explicit restart policy |
| Legacy line-based envelope | Add framed, versioned, bounded typed messages; keep a local compatibility adapter during migration |
| Polling/sleep drives all work | Use sosix events/timers with a bounded fallback poller; do not block the owner on a running job |
| Domain cleanup embedded in loops | Shared timer/task registration; test/cache policies remain registered domain callbacks |

For file-spool compatibility, use validated request IDs, private directories, bounded no-follow reads, atomic claim/publication, and an explicit recovery inventory. A duplicate with the same identity and same payload returns the retained outcome; the same identity with a changed payload is a protocol error. Transport redelivery must not imply side-effect replay.

Preserve the V2 transition oracle: do not jump from admitted directly to completed. An admitted operation with no published execution intent is different from an executing operation whose outcome is unknown. Inject crashes immediately before and after each state publication and native effect.

### 5.3 Journal policy and durability

The existing distributed-operation journal already validates immutable envelopes, writer ownership and transition ordering. Its recovery moves `executing` to `outcome-unknown`. Reuse that state machine rather than creating an agent-specific copy.

However, the current source explicitly promises **process-crash recovery, not power-loss fsync**, and bounds the retained event history to at most 100,000 events. A long-lived host cannot simply run forever on that history.

Required additions:

- Explicit durability profiles: `process-crash` and `power-loss`. The latter is accepted only when the storage adapter proves its file/directory/atomic-publication flush contract; otherwise fail configuration or select a clearly reported lower profile with prior policy approval.
- Checkpoint plus tail replay, checksummed/versioned manifests, monotonic sequence, and crash-safe switch of the current checkpoint reference.
- Retain unresolved operations, active runtime ownership, required result evidence, and dedupe tombstones across compaction.
- Set a documented retry/retention horizon. After terminal detail is expired, an old operation ID must be rejected as expired, not treated as a new create. Bound tombstones by authenticated epoch/sequence or an equivalent nonreusable-ID scheme.
- Quarantine corrupt or contradictory journals; do not fabricate empty state or delete the original evidence.
- Make full-disk and failed-publication failures explicit, and stop admitting mutations when state cannot be recorded.
- Keep the stable OS writer lock. Do not unlink and recreate a lock file while another owner may still hold it.
- Use independent journal roots/authority digests for independent domain owners. Sharing the implementation does not authorize cross-domain database writes.

With process-crash durability, a power failure or storage rollback can leave a valid older journal that omits newer ownership; this is not always detectable as a corrupt record. On boot/provider-generation change or unproven journal continuity, reconcile the entire managed runtime scope before new admission. Unmatched surviving/restarted resources remain quarantined and conservatively charged. Do not adopt or delete them from labels alone, and do not treat their capacity as free. If a rootless scope cannot inspect all machine resources, its machine-wide capacity authority must enforce the quarantine/delegation boundary.

Cancellation is two-stage: “accepted/requested” and “termination/reaping observed.” Releasing CPU/memory/device reservations requires the appropriate native absence/reaping evidence, not merely a cancel acknowledgement.

### 5.4 Shared service shape

The following are **proposed interfaces**, not claims about existing names:

| Port/value | Purpose | Implementation rule |
| --- | --- | --- |
| `DaemonService` | Lifecycle, readiness, draining, typed handler registration | Builds on owned service primitives |
| `OperationDispatcher` | Immutable envelopes, authorization, journal-backed idempotency | Uses distributed-control V2; no second state machine |
| `DaemonTransport` | Local IPC, file compatibility, authenticated remote channel | Separates framing from authority and domain payload |
| `TimerService` | Heartbeat, lease, retention, cleanup scheduling | Monotonic deadlines; bounded callbacks |
| `ExecutionOwner` | Start/cancel/recover/reap native processes | Uses group-process owner; handles never serialized |
| `StrictAdmissionLedger` | Local hard resource reservations | Separate policy from local task scheduler's progress overcommit |
| `DomainHandler` | Build/test/host/cache-specific work | Cannot bypass the owner of a different domain |

Prefer extracting pure values/codecs into `common/contracts` and keeping I/O in the appropriate sosix/nogc platform layers. Do not copy the current common-path I/O placement into every new module. Move code only where it reduces duplication and preserves import/ABI compatibility.

## 6. Unified SDN: IaC-only, orchestration-only, or both

### 6.1 Grammar versus schema

Existing SDN mapping/list/scalar syntax can represent the required documents. The work is strict schema dispatch, typed values, validation, planning and execution—not new lexical grammar. Reuse `parse_with_spans_and_issues` once per input.

Preserve existing `orchestration.simple/v1alpha1` Pod/Deployment and `ci.simple/v1alpha1` Job/Pipeline behavior. New kinds may use the same group/version when that is a compatible addition; any changed meaning of an existing field requires a new explicit version and checked conversion.

| Resource kind | Meaning | Status in this plan |
| --- | --- | --- |
| Pod / Deployment | Existing workload declarations | Preserve existing subset and strictness |
| Job / Pipeline | Existing CI finite work and dependencies | Preserve domain behavior |
| ResourceProfile | Min/recommend/prefer/limit and resource-sharing policy | Proposed typed kind |
| HostPool | Eligible hosts, trust and capability requirements | Proposed typed kind; not proof a host exists |
| RuntimeClass | Approved provider/isolation/capability policy | Proposed resource integration; existing runtime-class strings remain meaningful |
| AgentSession | Interactive agent intent, workspace, profile and terminal policy | Proposed typed kind |
| HostConfig | Local daemon configuration and enrollment references | Proposed administrative kind; never self-authorizes enrollment |
| ResourceList | `spec.items` of independently typed resources | Proposed common envelope |

Infrastructure-only application creates/updates approved configuration and profiles without launching workloads. It does not implicitly install packages, enable OS features, or create machines. Provisioning providers may be added later as separately authorized resources with a visible plan.

Orchestration-only input references already admitted profiles or uses existing Pod resources. Combined input validates all items and references before any apply. Validation can be atomic; external provisioning and container creation across hosts are not an atomic transaction. Report partial application and use exact compensating actions.

### 6.2 Decode and resolution rules

1. Parse each file once with spans/issues.
2. Validate the strict resource envelope and flatten ResourceList values without serialize-and-reparse.
3. Dispatch by exact `(apiVersion, kind)`; reject unsupported kinds and unknown fields.
4. Resolve identity by group/kind/namespace/name, enforce reference scope/RBAC, and reject duplicates, cycles and missing references.
5. Resolve template/profile revisions to immutable versions. Later edits affect a new plan, not an already launched attempt.
6. Normalize CPU to millicores, memory/storage to bytes, and device claims to typed identities. Reject overflow, negative values and ambiguous units.
7. Resolve resources and provider capabilities into an immutable plan with a cryptographic digest.
8. Apply only the authorized plan digest and expected desired-state revision. Separate dry-run from effects.
9. Preserve errors such as `spec.items.2.spec.resources.memory.min` with original line/column.
10. Generate SDN LSP completion, hover, references and diagnostics from the same schema definitions; do not maintain a separate permissive editor schema.

If Simple code constructs manifests, its typed builder must produce this same ResourceSet/plan and run the same validation/authorization path. SDN is the serialized format, not a second semantics engine. Do not evaluate arbitrary SPL or shell expressions while loading an SDN document.

### 6.3 Proposed combined example

This is a **design example for the new kinds and fields**. Current strict decoders do not accept it as a complete runnable resource set. The image placeholder must be resolved to an allowed immutable digest before apply.

~~~sdn
apiVersion: orchestration.simple/v1alpha1
kind: ResourceList
metadata:
    name: caret-development
spec:
    items:
        - apiVersion: orchestration.simple/v1alpha1
          kind: ResourceProfile
          metadata:
              name: agent-cpu
              namespace: caret
          spec:
              cpu:
                  min: "1000m"
                  recommend: "2000m"
                  prefer: "4000m"
                  limit: "4000m"
              memory:
                  min: "2Gi"
                  recommend: "4Gi"
                  prefer: "8Gi"
                  limit: "8Gi"
              gpu:
                  required: false
              placement:
                  preserveScarceGpuHosts: true
        - apiVersion: orchestration.simple/v1alpha1
          kind: AgentSession
          metadata:
              name: review-simple
              namespace: caret
          spec:
              resourceProfileRef: agent-cpu
              hostPoolRef: development-linux
              runtimeClassRef: podman-rootless
              agent:
                  provider: codex
                  taskRef: task-immutable-42
              workspace:
                  repositoryRef: simple-approved
                  revisionRef: reviewed-input-revision
                  isolation: worktree
                  retention: retain-on-failure-or-dirty
              session:
                  frontend: smux
                  persistent: true
                  disconnectPolicy: retain
              template:
                  os:
                      name: linux
                  containers:
                      - name: agent
                        image: "registry.example/simple-agent:resolved-before-apply"
~~~

The approved host pool, runtime class, repository, task and revision references must already resolve, or be included in the same resource set. Secret values never appear here. The selected agent adapter supplies typed executable/argv from a verified installed CLI capability; task text is not interpolated into a shell command.

An IaC-only file can contain just the ResourceProfile. An orchestration-only file can contain AgentSession with a preexisting profile, or an unchanged existing Pod/Job. No second authoring language is required.

### 6.4 Resource meaning

For a CPU/memory profile, require `min <= recommend <= prefer <= limit`; omitted recommend defaults to min, omitted prefer to recommend, and omitted limit to prefer. These are proposed explicit defaults, not a reinterpretation of existing requests/limits.

| Field | Meaning |
| --- | --- |
| min | Hard floor for an admitted allocation; never silently reduced |
| recommend | Normal useful allocation; scheduling aims here before accepting constrained admission |
| prefer | Opportunistic upper target when capacity/fairness permit |
| limit | Requested maximum ceiling; not a promise that this much resource is reserved |
| effective allocation | Exact reserved/enforced values committed in the attempt's grant |
| effective limit | Provider-enforced ceiling recorded in the grant and user-visible status |

Initial policy is **strict no-overcommit reservation with enforced caps**: choose an allocation between min and prefer, then use that allocation as both the reservation and effective cap. A profile limit is the maximum allowed cap, not an automatic larger cap after selecting a smaller allocation. An explicit later burstable policy may separate reservation and cap; memory overcommit then needs a separately approved policy.

This is an admission/accounting guarantee, not a promise of dedicated cores, minimum execution speed, locked physical memory or immunity from OOM. Podman CPU quota is an upper consumption bound [W12]. Dedicated CPU entitlement requires a separately qualified host-partition/cpuset policy, and host/system/unmanaged pressure still needs accounting and safety margins.

Existing Pod `requests/limits` keep their current meanings. In a strict host pool, account memory at its enforced maximum and CPU according to that pool's declared reservation policy; do not allow a profile conversion to erase an existing hard limit. Reject conflicting explicit profile and inline values unless a documented typed override rule resolves them.

## 7. Scheduling and resource allocation

### 7.1 Host eligibility and scoring

Hard filtering precedes preference scoring:

- Execution OS/architecture, physical-host requirements, runtime/isolation class and image/toolchain compatibility.
- Current authorization, trust class, usable device capabilities and enforcement capabilities.
- Minimum CPU/memory/storage/PID/network/port and GPU claims, including host/service overhead.
- Workspace placement and data-access policy, tenant/project quotas, draining and health state.

Then score feasible candidates by queue fairness, scarce GPU preservation, data/image/cache locality, resource fit, recommendation satisfaction, and stable tie-breaks. Explain each rejection and the final score components. Do not let a stale cached label override a current host refusal.

Use `allocatable = enforceable capacity - host/system reserve - active reservations - uncertainty reserve`. Telemetry is a secondary pressure signal, not a replacement for reservation accounting. Reservations for uncertain running work remain charged until reconciled or externally fenced.

The existing local fiber scheduler may continue its domain-specific progress policy. The host/global admission path must use strict checked arithmetic and atomic reservation updates; no “run one anyway” memory escape hatch.

### 7.2 GPU-constrained example

Suppose the only eligible GPU host has 8 CPU cores and 24 GiB of **workload allocatable** memory after host overhead. Four tasks each declare min 1 core/2 GiB, recommend 2 cores/4 GiB, prefer 4 cores/8 GiB.

| Device situation | Valid outcome |
| --- | --- |
| Each task needs the one whole exclusive GPU | One runs; others queue, regardless of spare CPU/RAM |
| Four qualified independent device partitions exist | Four may run if each partition meets its claim and CPU/RAM admission passes |
| Explicit shared-GPU mode allows four clients | Four may receive 2 cores/4 GiB each, subject to the shared-mode risk policy |
| A task only calls a remote inference endpoint | Usually no local GPU claim; schedule it on a CPU host unless another task step needs a GPU |
| CPU/RAM pressure rises before admission | Reduce a new allocation toward min, or queue it; do not reduce an existing process's memory cap automatically |

NVIDIA time slicing does not provide the same memory/fault isolation as MIG, and a larger count of time-slice requests does not guarantee proportional compute [W05]. Therefore GPU claims must specify exclusive/partition/shared mode, supported device/profile, and any enforceable memory requirement. Do not treat a VRAM estimate as an enforced limit.

An optional GPU preference can fall back to CPU only if the workload explicitly declares a CPU-capable execution alternative. Required GPU work must never be silently downgraded.

### 7.3 Placement versus domain scheduling

Build/test parents release ready work; the orchestrator places it. The host admits and runs it; it does not recompute a build graph. This avoids three independent schedulers fighting over priorities or retrying the same action.

Support priority bands with aging and per-project fairness. Preemption is initially opt-in for restartable/checkpointable work; interactive agent sessions default to non-preemptible. Stop acceptance is not enough to transfer a GPU to another task.

### 7.4 Assignment protocol

1. Orchestrator persists desired workload and immutable plan.
2. It selects a host and records a tentative grant with an assignment generation and operation ID.
3. Host verifies authority, epoch, boot/provider generation and current physical-scope capacity, then durably prepares a reservation with a unique nonce, revision, allocation and deadline.
4. Host returns that exact reservation receipt; controller commits the assignment and sends an execution authorization bound to its nonce/revision, assignment generation, allocation and immutable plan.
5. Host atomically checks that the reservation is still valid and consumes it into committed/executing state before launch. Persist the execution intent under the same authority, ideally with ledger state as a projection of one journal transaction; an alternative needs a proved recovery protocol that holds capacity until both records reconcile. Then call the provider once or reconcile a prior uncertain call.
6. Runtime and smux identities are bound into the attempt/session receipt.
7. Host reports observed state; controller validates identity and transition before acceptance.
8. Release compute/device capacity only on its required termination/native absence evidence. Retained worktrees, volumes, image storage and network endpoints keep their respective reservations until their own cleanup/retention owner confirms release.

This is an idempotent, recoverable handshake, not a claim of distributed ACID. Prepared-but-uncommitted reservations may expire under a defined protocol. A delayed execution authorization after expiry/abort/release is rejected without effects, even if its original signature is valid. Duplicate authorization resolves the retained operation, not a new launch. Once execution may have started, a lease timeout alone cannot make resources free.

## 8. Host daemon: detailed design

### 8.1 Registration and inventory

The local HostConfig supplies controller references, approved runtime choices, budget policy, identity references and workspace roots. Enrollment requires an administrator-approved bootstrap or existing configured credential; knowing a host name is not authority.

Advertise:

- Stable physical host ID, service/user scope, delegated budget/device identity, OS boot identity, service incarnation and provider generation.
- Physical OS/edition/build/architecture separately from supported execution OS/architecture.
- Runtime binary/API versions, image store scope, usable isolation classes and verified features.
- CPU/memory/storage allocatable budgets, GPU identities/profiles/sharing modes and resource overhead.
- Network, filesystem, TTY/exec, resource-limit, process-tree-reap and durability capabilities.
- Health/readiness, drain state, capability revision and active/uncertain reservations.

Separate a lightweight liveness heartbeat from larger capability and status updates. Renew authority on an authenticated channel, use monotonic local deadlines, and do not compare different hosts' monotonic timestamps as if they share a clock.

### 8.2 Runtime composition

The host's execution coordinator:

1. Resolves a typed grant and exact approved provider.
2. Prepares private workspace, immutable input, secret references and read-only shared cache access.
3. Journals each external mutation before it may occur.
4. Calls Simple Container through typed operations, preserving native identity and uncertainty.
5. Creates/binds an smux session through the typed port, passing a terminal transport—not a raw engine credential.
6. Watches runtime and process-owner events and reports bounded state changes.
7. Coordinates cancel/drain/cleanup and retains unresolved resources.

Keep container-runtime survival independent from a short-lived RPC connection. A host-daemon restart can recover a surviving runtime, but recovering smux metadata is not proof that a lost native PTY/process can be resurrected.

### 8.3 Transport and service installation

First remote delivery should use an authenticated existing SSH transport or equivalent configured secure tunnel, keeping loopback mux/runtime endpoints private. Native remote service transport can follow with mutual authentication, certificate rotation, namespace/operation-scoped grants and revocation. A tunnel does not remove the need for application authorization.

| Platform | Service packaging | Privilege boundary |
| --- | --- | --- |
| Linux | systemd user service/socket or approved system service | Rootless Podman first; dedicated privileged operations only when explicitly configured |
| Windows | SCM-managed service plus narrow broker/client IPC as needed | Restrict named-pipe ACLs; do not grant agent users unrestricted Docker daemon access |
| FreeBSD | rc.d service and narrowly scoped privileged jail broker | Jail/VNET/filesystem setup needs approved authority |
| macOS | launchd service using approved Apple/native provider | Signing/entitlements and runtime access remain explicit |

These are packaging adapters around shared service code, not four independent daemon implementations. “Host daemon written in Simple” does not mean that Docker, Podman, Apple services or kernel facilities disappear.

### 8.4 Operational commands

Provide typed API operations and corresponding CLI/MCP surfaces for enroll, inspect, capability report, list-owned, drain, resume, reconcile, explain-blocked and shutdown. Exact command names can follow the existing CLI conventions.

An update uses drain, protocol compatibility check, journal handover and new service incarnation. Do not upgrade the provider runtime beneath active work unless its survival/recovery behavior is qualified. An incompatible journal or protocol version blocks startup rather than being rewritten by an older binary.

## 9. What Simple Container must add

### 9.1 Required provider interface

Preserve existing runtime identity/intent/result types and introduce versioned lifecycle/stream interfaces where the probe-only trait is insufficient. Platform leaves remain the mutation owners.

| Capability | Simple Container addition | Host/orchestrator responsibility |
| --- | --- | --- |
| Probe | Structured usable capabilities, versions, enforcement and caller authority | Cache by capability generation; filter/refresh |
| Prepare/create/start | Immutable typed request, exact runtime ID and intent reconciliation | Grant, assignment and local reservation |
| Workspace/mounts | Canonical allowed roots, read-only/read-write, UID/ACL handling, no-follow checks | Repo/revision policy and ownership inventory |
| Environment/secrets | Allowlisted env, private secret injection, redact receipts/logs | Secret authorization, expiry and rotation |
| Working directory | Validated path within mounted workspace | Select workspace identity |
| Image/command | Digest resolution and exact ENTRYPOINT/CMD/argv semantics | Approved template/provider selection |
| Exec/attach | Typed exec identity, streaming handle, EOF, signal/control and resize capabilities | Bind to smux; authorize attachments |
| Stats | Bounded CPU/memory/PID/I/O/device data or explicit unsupported | Pressure and accounting diagnostics |
| Resource limits | Prove requested CPU/memory/PID/storage/device enforcement | Choose effective grant and ceiling |
| Stop/destroy | Graceful deadline, force policy, exact-ID absence and cleanup receipts | Retain reservation until proof; decide workspace retention |
| Recovery | Inspect exact owned identity; return unknown when evidence is insufficient | Fence attempts and reconcile across restarts |
| Networking | Explicit supported network profile, ports and cleanup ownership | Policy, endpoint authorization and placement |

Do not add enrollment, cluster queues, project priorities, task dependencies or terminal UI to Simple Container. A standalone library/CLI remains valid; orchestration is composition above it.

### 9.2 Linux Podman first

Reuse `LinuxOciRuntimeProviderV1`, its journals and the existing CI wiring. Make Podman an explicit selected provider, not “whichever executable prints a version first.”

Required work:

- Probe rootless usability, user namespace/sub-ID setup, cgroup delegation, storage/network backends and effective limits. A version string is insufficient.
- Add mounted worktrees, controlled cache/artifact access, working directory, env/secret references and user mappings.
- Keep read-only rootfs where requested, but provision private writable HOME/XDG/config/state/temp/runtime locations for the CLI. Bound bytes/inodes, charge tmpfs against memory and define which resume state survives an attempt. Never mount the host user's whole home or credential directory to make a CLI work.
- Add reliable non-TTY output and interactive TTY/exec/resize, with bounded streaming and terminal ownership.
- Add stats and device-claim integration. Use a supported device mechanism such as qualified CDI where available; never infer GPU access merely from a host GPU listing.
- Verify command versus image entrypoint behavior. The inspected command builder appends command/args after the image; it must pass explicit ENTRYPOINT/CMD override tests before claiming Kubernetes-equivalent semantics.
- Use typed argv or a qualified local API client. An explicit shell command is a workload choice, not a transport convenience.
- Keep the Podman API socket private. Its access grants broad execution authority as the service user [W01]; do not mount it into an agent container.
- Remove automatic whole-runtime volume pruning. Destroy only resources recorded under the exact workload/attempt/owner and recheck ownership before deletion.
- Keep unsupported rootless network, device or hard-limit requests blocked; do not silently elevate or fall back to a bare host process.

The first interactive milestone is one container/one agent session. Multi-container Pods need an explicit later capability and lifecycle policy; reject them in a provider that only supports the single-container subset.

### 9.3 Windows Docker process hardening

The older canonical Windows design selected containerd/runhcs. **This plan intentionally changes the first provider bridge to Docker because that is the user's chosen implementation path.** Reuse the policy/identity design, update the conflicting architecture/detail/test documents, and keep the bridge replaceable.

P0/P1 requirements:

1. Discover the actual Windows engine, OS edition/build, Containers feature, caller permissions and engine health. Reject an unintended Linux Docker endpoint.
2. Pin image digest and validate image OS metadata against the supported host/image process-isolation matrix. Windows 11 development support is a separately qualified lane, not blanket Windows Server production support [W02–W04].
3. Explicitly request process isolation and inspect the actual result. Never silently choose Hyper-V, WSL/Linux VM, HostProcess or native host process.
4. Use typed argv/Engine API operations, Windows path/ACL validation and correct argument serialization. Do not compose PowerShell or cmd strings from task input.
5. Run with the least-privileged supported container identity, controlled mounts and secret access. A process-isolated container shares the host kernel; do not advertise it as a hostile multi-tenant security boundary.
6. Record Docker native ID, workload/attempt, node boot, provider generation and operation ID. Name/label is a discovery aid, not sole deletion authority.
7. Qualify exec/TTY, resize, UTF-8, disconnect, CTRL/signal differences, engine restart, timeout and exact stop/delete.
8. Verify enforcement of CPU/memory/PID or any advertised limits; account platform overhead. Unsupported requirements fail admission.
9. Treat partial network/volume/process cleanup as pending. A failed removal must not become “success” merely because the CLI call returned.
10. Eliminate runtime-global prune and test-daemon name-only cleanup. No broad Docker pipe permission should be delegated to an agent.

Do not claim Windows ARM support by analogy with x86. Advertise only the installed engine/image/architecture pairs that pass the matrix.

Include the user's previously specified **Windows 11 Enterprise 23H2, build 22631.3527, with a Server Core 2022 image and process isolation only** as an explicit development/test fixture, if that remains the selected machine. Pin the actual offline engine and image digest when testing. This recorded configuration is not proof of compatibility, support lifecycle, current patch level or production qualification; do not silently upgrade it or substitute Hyper-V to obtain a passing result.

### 9.4 FreeBSD and Apple

FreeBSD provider: own jail identity, jail root/image provenance, devfs policy, VNET or explicitly shared networking, rctl/resource capability checks, exec/PTY, exact teardown and crash recovery. Privileged creation may use a narrow broker; a configured jail is not automatically rootless. FreeBSD Linux-compatibility jails are a separate optional capability and do not imply generic Linux OCI compatibility [W06].

Apple provider: use the official container runtime as an explicit `apple-linux-vm` lane. Model host OS macOS, execution OS Linux and VM overhead separately. Check installed Apple silicon/macOS/runtime requirements and supported mounts/network/exec behavior. Do not advertise native macOS execution or GPU passthrough without evidence [W07].

Native macOS work requires its own trusted-process or qualified sandbox lane; Apple Linux containers cannot execute native macOS toolchains merely because the physical host is a Mac. Preserve the native Simple Container VM-rejection boundary and route VM work through an explicitly different runtime class.

## 10. Reusing an existing Kubernetes control plane

The choice is not “implement everything ourselves or Kubernetes is impossible.”

| Mode | Placement/runtime authority | Simple work still required |
| --- | --- | --- |
| Native Simple-managed pool | Simple Orchestrator + host daemon + provider | Shared service hardening, scheduling, heterogeneous adapters and Caret/smux binding |
| Existing Kubernetes cluster | Kubernetes scheduler/kubelet/runtime | SDN translation/controller, identity/status mapping, terminal owner, workspace/secret integration and policy |
| Apple experimental cluster | Kubernetes inside Apple-backed Linux VMs | Version-qualified cluster adapter and the same Caret/mux integration; account VM boundaries |
| FreeBSD jail/native macOS pool | Qualified host provider | Explicit native lane; not a stock Kubernetes Linux/Windows worker merely by registration |

Kubernetes documents Linux and Windows workers, with its Windows-specific support/limitations [W08]. Podman is not itself a Kubernetes scheduler, and accepting some Kubernetes-shaped input does not imply complete Kubernetes behavior.

Apple's current-branch command reference documents experimental `container cluster` management with Linux VM-backed Kubernetes nodes [W09]. It also warns that current-branch documentation is not necessarily released behavior. Therefore probe the installed release, keep this feature optional, and do not make the first Podman delivery depend on it.

For Kubernetes mode:

- Translate only an explicitly supported subset. Reject unsupported native isolation, device and filesystem semantics; never silently drop fields.
- Simple may choose a cluster/pool and enforce project-level policy; Kubernetes owns node placement and actual node resources.
- Do not reserve the same physical capacity in both a Simple native ledger and a Kubernetes node ledger. Use disjoint resource pools or a single qualified capacity authority.
- Model Kubernetes resource UID, namespace, resource version, Pod UID and container/exec identity in receipts; names are insufficient.
- Give terminal persistence an owner that survives client disconnect. A raw API exec connection alone is not an smux replacement.
- Do not claim safe retry solely because a Kubernetes API object was deleted. A partitioned process may still run; Kubernetes documents analogous duplicate-identity dangers with forced Pod deletion [W10].
- Keep Kubernetes cluster credentials at the approved adapter boundary; agent containers do not need them.

Initial recommendation: finish the native Podman workflow using existing Simple contracts, while keeping an execution-backend port suitable for Kubernetes. Implement Kubernetes first instead only when an already-operated cluster is the user's preferred operational authority; this changes the execution adapter, not the Caret session model.

## 11. smux: one local/remote session model

### 11.1 Preserve the terminal port

`CoreMuxV1` already supplies connect, query, execute, poll-events and disconnect, plus typed launch/attachment operations. Use that port as the terminal boundary. Do not teach smux how to score hosts, parse IaC, resolve GPU preferences or operate arbitrary container engines.

The Caret session-creation facade gains two targets:

- **Local:** the existing local execution path, qualified separately per backend/version.
- **Orchestrated:** submit an AgentSession plan, receive a pending logical-session handle, then resolve it to an authorized CoreMux endpoint and attachment ticket once placed.

A proposed `OrchestratedSessionPort` provides submit/status/cancel-request/resolve-attachment. This is a small orchestration adapter above CoreMux, not a second terminal protocol. Do not overload an existing local `CreateSessionV1` with hidden network scheduling.

Cancellation of a pending session is a durable desired-state operation. Before assignment it removes eligibility to launch; during reservation/preparation it aborts or reconciles that exact attempt; after execution may have started it becomes exact stop/reap-pending. A late placement/ready notification cannot resurrect a cancelled request or make Caret forget an orphaned process.

### 11.2 Execution binding and stream ownership

Extend the existing `SessionExecutionBindingV2` through a new versioned execution-binding union, not by making its native-process checks optional everywhere. Preserve V2's positive PID/process-start validation for native-process bindings. The new binding discriminates **native process** from **runtime execution**: a container primary process/exec or Kubernetes execution uses exact provider/resource/exec evidence, which may not expose a portable PID/start timestamp. A host-side `podman exec` or attach helper PID is transport identity, not the agent identity.

Retain stable session generation, host/boot/service and request/ticket bindings where applicable, then add:

- Workload UID and immutable spec digest.
- Attempt ID/generation and assignment fence.
- Resource-grant ID/revision.
- Runtime provider/native ID and provider generation.
- Workspace ID/revision and retention policy.
- Transport/session-owner incarnation and its negotiated transport capabilities.

Moving replay cursors belong to per-attachment resume state, not immutable execution-binding equality. Different viewers may have different positions without changing the workload identity or invalidating control leases.

Persistent metadata is not a live native lease or permission to adopt a process. The owner resolves live capabilities from authoritative local state.

Provider execution stream handles remain in a persistent local terminal owner/platform leaf: smux itself or a qualified single-owner terminal broker whose lifetime is independent of a host RPC connection. smux is their exclusive logical consumer/controller. The host must not independently drain the same stdout/PTY as smux. If logs need fan-out, derive them from the owner stream with bounded independent cursors.

For container execution, avoid “host PTY attached to an exec process that also creates a second unrelated terminal emulator.” Select one explicit transport:

1. Provider-managed interactive exec/attach bytes and resize, consumed by smux; or
2. A qualified in-workload terminal owner, exposed through the same CoreMux adapter.

Record which component owns the native PTY, child lifecycle and resize operation. Common terminal rendering stays in smux. No native handles cross host boundaries.

For the initial provider profile, prefer the chosen agent as the container's primary command with a qualified persistent attach path. If an exec-in-existing-container profile is selected instead, declare the primary/keeper process, exec identity and container lifetime explicitly. Container-running is not evidence that the agent exec is still running, and agent-exec exit need not mean the keeper container has exited.

If a provider cannot keep the native transport alive across host-daemon restart, advertise and test reconnect/gap/loss behavior explicitly. A separate smux process does not magically preserve a stream whose sole native owner died inside the host daemon.

### 11.3 Once-only startup and binding

The current `MuxCreateSessionV1` requires a launch; it cannot simply adopt an already-started container agent [S25]. For orchestrated execution, add an authenticated, versioned owner-side **bind-existing-runtime-execution** operation. It receives an exact host-issued execution/stream capability and never starts a second agent. Acquire this extension explicitly; an unsupported owner rejects the request.

Startup protocol:

1. Persist one logical session/start plan, workload/attempt identity and idempotency key.
2. Host reserves resources and journals the exact provider create/start intent.
3. Provider starts or reconciles that one runtime execution and establishes the declared persistent transport/buffering path.
4. smux binds that exact execution/transport capability once and durably records its binding receipt. Duplicate bind returns that binding; changed execution identity requires an explicitly new generation.
5. Publish ready/attachment information only after matching provider and smux receipts exist.

Crash after runtime start but before binding means reconcile-and-bind, not launch-again. Crash after binding but before ready publication means recover the existing binding receipt. If early-output capture is unavailable or a transport reconnect loses bytes, report the gap; do not claim a complete transcript. Test every boundary, including host-daemon death while smux and the workload remain alive.

### 11.4 Complete existing unfinished integration

1. Finish the typed framed owner dispatch described by the mux wire design; retain legacy local protocol behind a compatibility adapter.
2. Test typed client/server interoperability and protocol negotiation; authored tests are not runtime evidence.
3. Replace hardcoded provider `process` and generation `1` with actual execution bindings.
4. Route Caret's direct smux imports, independent process launch, Unix tmux workspace path and terminal projection through the common session abstraction.
5. Use the current loopback-only client through an approved secure tunnel first. Native remote address support requires authenticated endpoint discovery and a reviewed transport, not simply allowing arbitrary host strings.
6. Initially use the existing metadata events plus rendered Capture/owner-issued content-revision continuation. `ContentAvailable` is not raw terminal data, and event cursors are not byte positions [S36]. If raw streaming/replay is required, add a separately negotiated terminal extension with stream epoch, byte offsets, bounded history, snapshot/delta synchronization, gaps and backpressure. Preserve byte order and partial UTF-8 correctly.
7. Reconnect only after checking host, boot, service, provider and session generations. A mismatch is a new binding, not a successful continuation.

CoreMux's expired/revoked-lease rule remains exact: only retained receipt recovery with the original token, owner incarnation and already-bound request ID is permitted, using RequestStatus or an identical disconnect replay. It grants no new mutation, capture, event access or renewal. Evicted history is Unknown, not NotApplied; after receipt retention expires the old token has no access. A fresh connection must not blindly resubmit CreateSession to resolve an unknown old result.

### 11.5 Control actions stay distinct

| User action | Authority | Effect |
| --- | --- | --- |
| Close/detach pane | Attachment client | Stops this attachment; workload normally continues |
| Cancel pending session | Orchestration desired-state owner | Prevents launch or transitions an already-started attempt to exact stop/reap-pending |
| Cancel agent turn | Provider/session control | Sends the supported interrupt; may leave the CLI available |
| Cancel build/test job | Build/test domain owner | Cancels the job and its exact attempt tree |
| Terminate session | Workload/session owner | Coordinates agent exit, container stop and terminal closure |
| Delete history | History owner | Removes permitted transcript metadata; does not imply process termination |
| Delete workspace | Workspace owner, explicit retention authorization | Separately checks dirty state, references and ownership |
| Resize | Current geometry-lease holder | Changes terminal geometry, not input authority |
| Send input | Current input-lease holder | Writes bytes/input to the bound session |

The existing V2 action scope maps CancelJob to the build domain. Agent-workload cancellation must obtain its own correctly typed domain/grant mapping rather than reusing `build_cancel` by convenience.

Multiple viewers may attach, but input and geometry ownership remain separate leases. Reattachment does not automatically steal them. Lease expiry uses the issuing owner's monotonic clock and current revision.

## 12. Caret suite: user-facing and adapter work

### 12.1 Session creation experience

The same “new session” action should accept local execution or a named SDN template/resource file. In orchestrated mode, expose:

1. Agent provider and requested task/command.
2. Repository/revision or immutable input snapshot.
3. IaC template/profile and permitted overrides.
4. Requested versus effective resources, runtime/isolation and host or cluster.
5. Queue/admission explanation and pending authentication/approval state.
6. Terminal attach when ready; reconnect to the same logical session on client return.

Caret submits a typed task and immutable plan reference. It must not turn the user's task into a host shell command, pass an entire credential directory, or claim that a terminal is running before the host confirms it.

### 12.2 Provider-specific CLI integration

The inspected `agent_plan.spl` has a Codex-specific branch and otherwise uses Claude-style arguments. Replace that fallback with explicit provider adapters for each supported Codex/Claude/Gemini/Kimi version family.

Each adapter declares:

- Executable/version detection and supported OS/architecture.
- Interactive and noninteractive launch forms with typed argv.
- Task injection via supported stdin, private file or documented argument.
- Authentication/bootstrap flow, selected account reference and credential lifetime.
- Provider conversation/resume identifier, if supported, and its trust boundary.
- Interrupt/exit behavior, approval prompts, tool permissions and exit-code mapping.
- Structured events/output when available; otherwise honest terminal-only capabilities.
- Resume-after-process-exit versus attach-to-still-running-process as distinct operations.

Unknown or incompatible versions return a visible unsupported-provider result. Never pass a guessed flag from another CLI. The orchestrator does not need to understand a provider's conversation protocol.

### 12.3 Caret/suite integration

Converge pane manager, workspace manager, agent manager and distributed workbench on the same immutable execution binding. Existing descriptors are not active services: wire them to real adapters and test failure paths.

Add:

- Resource/template browser and SDN diagnostics, with read-only dry-run/placement explanation.
- Queued, preparing, running, waiting-for-input, disconnected, outcome-unknown, exited and cleanup-pending distinctions.
- Safe multi-session selection, host/runtime filters, per-attempt logs and workspace retention visibility.
- Explicit account/secret references and approval surfaces; no credentials in terminal titles or ordinary receipts.
- Cancel/terminate actions that show their exact scope and do not confuse closing a pane with killing work.
- Provider session history association without treating history as native-process authority.
- CLI and MCP parity for create/list/inspect/attach/detach/cancel/terminate/explain. Background tasks and interactive tasks use the same workload identity.
- Notifications for scheduling failure, approval required, completion and retained dirty worktree.

Spipe configuration may supply approved agent/toolchain/template defaults, but configuration precedence must be explicit and captured in the plan digest. Runtime changes to user/host/project settings must not silently mutate an active attempt.

### 12.4 Proposed interaction contract

The names below describe proposed operations, not already-implemented CLI commands.

| Caller | Operation | Result and ownership |
| --- | --- | --- |
| Caret/CLI/MCP | Validate resource set and request a plan | Typed diagnostics or immutable plan digest; no effects |
| Caret session facade | Submit AgentSession with plan/task and idempotency ID | Pending logical session/workload identity |
| Session facade | Watch admission/placement/attempt status | Effective grant, waiting reason or exact failure |
| Session facade | Resolve authorized attachment | Bound CoreMux endpoint/ticket plus expected session generation |
| Caret terminal client | Connect/query/attach through CoreMux | Owner-issued attachment and separate input/geometry leases |
| Caret terminal client | Disconnect | Attachment ends; workload retention follows its explicit policy |
| Caret workload client | Request termination | Stop-pending receipt, then confirmed execution and cleanup outcomes |

An ordinary approved template can make this one “new session” action in the UI. A changed infrastructure/provisioning plan or elevated permission remains a separate approval boundary; the familiar smux-like UI must not hide additional authority.

## 13. Build/test runner integration and shared code migration

### 13.1 Preserve domain authorities

| Consumer | Shared infrastructure to use | Domain logic that remains local to it |
| --- | --- | --- |
| Test light/generic daemon | Owned service lifecycle, request journal, transport, timers, execution owner | Test selection, fixture/reset policy, warm workers, stale test-session cleanup |
| BuildRunner | Task journal, executor adapter, bounded dispatch, exact cancellation and remote receipt validation | DAG dependencies, affected actions, toolchain/input binding, verdict and output publication |
| CI pipeline | Provider lifecycle adapter, grants, logs, recovery and exact cleanup | Pipeline dependency semantics and job verdict acceptance |
| Cache daemon | Owned service shell, protocol limits and health/transport primitives | Semantic cache keys, immutable publication, trusted index ownership and retention |
| Host daemon | Distributed operation journal, strict ledger, providers and service shell | Local capability/assignment/recovery policy |
| smux | Service lifecycle and transport primitives where compatible | Terminal/session ownership and attachment leases |

Do not merge test-runner state into the host's workload table just because both have “running” states. Share codecs and execution mechanisms; give each domain its own transition oracle, store and accepted evidence.

### 13.2 Existing entrypoints require deliberate convergence

The inspected test CLI launches `light_daemon.spl`; the generic SDK daemon is a separate route. First document which command selects which route. Keep the current lightweight path available until the shared service route passes startup, warm-state, response-loss and cancellation tests.

The BuildRunner entrypoint is a finite CLI, not a permanently running shared daemon. It should be able to use the shared library in-process for local work and a host/orchestrator client for remote work without requiring a new always-running service for every invocation.

The cache daemon remains a separately owned service. A host receiving remote execution output does not gain permission to write directly into the parent's trusted cache index.

### 13.3 One executor adapter, multiple targets

Define or extend an execution adapter that accepts immutable action/test intent and yields an attempt handle plus typed events/evidence. Targets are local process, local container, or orchestrated attempt. Do not embed a remote scheduler inside each build/test worker.

Before routing remotely:

1. Parent freezes action identity, input revision/digests, toolchain/target and output contract.
2. Parent creates a child execution request with explicit resource and isolation needs.
3. Host/runtime returns exact attempt/runtime/process-tree evidence and bounded output manifests.
4. Parent verifies execution authority, input/toolchain match, completeness, output digests and attempt generation.
5. Only the parent publishes an accepted verdict and trusted outputs/cache entries.

The current build database session explicitly rejects remote evidence. Preserve that guard until a separately tested verified-remote path is implemented. Deleting the check is not remote execution support.

For tests, distinguish a normal process exit from a valid test-result envelope. Validate expected test inventory, framework/version, timeout/cancel state and reset evidence. A container exit code alone must not promote missing tests to a pass.

### 13.4 Reuse without regression

- Keep TaskRunner V1 restricted to build/test. Reuse generic distributed V2 operations for agents and introduce new versioned workload values only for missing semantics.
- Retain existing local cache and fast paths. Orchestration is optional when local execution is selected.
- Migrate shell-based test-container adapters to the typed provider; remove name-only lifecycle and global prune.
- Preserve exact process-tree cancellation/reaping. Container stop/delete and host-side client reaping are different evidence.
- Keep per-attempt workspaces and immutable artifact/cache access; never let two independent agents edit one worktree implicitly.
- Add policy architecture tests preventing app-layer direct process/runtime calls that bypass the approved execution owner.

## 14. State, recovery, and failure semantics

### 14.1 Separate state projections

| State domain | Examples | Meaning |
| --- | --- | --- |
| Desired resource | Admitted, changed, deletion requested | User/controller intent |
| Scheduling | Queued, reserved, assigned, blocked | Resource and placement state |
| Operation journal | Admitted, executing, outcome-unknown, completed/failed/cancelled | Whether a specific immutable mutation has an authoritative outcome |
| Runtime attempt | Preparing, running, exited, stop-pending, absent, uncertain | Observed native execution |
| Terminal | Created, attached, detached, ended, replay-gap | Session/transport state |
| Workspace | Active, retained, cleanup-pending, removed | Data lifecycle |

These are explanatory projections, not a replacement of existing versioned enums. A UI may combine them, but persistence and acceptance must not collapse them into a single misleading “done” flag.

### 14.2 Failure matrix

| Event | Required behavior | Forbidden shortcut |
| --- | --- | --- |
| Submit/create response lost | Query retained operation outcome; retry same immutable ID | Start a second agent with a new ID automatically |
| Mux create reply lost and lease expired | Original-bound receipt-only recovery; unknown if history is gone | Replay CreateSession with an expired token or assume NotApplied |
| Same ID, different payload | Reject payload mismatch | Last-wins replacement |
| Crash after native create before response | Recover intent and inspect exact owned native identity | Assume create failed because no response exists |
| Host heartbeat expires | Mark suspect/unreachable; preserve uncertain reservations | Assume process is dead and reassign exclusive work immediately |
| Old host returns after replacement | Reject stale fences/results and reconcile old resources | Adopt stale state because the hostname matches |
| Controller restart | Replay desired state/assignments; reconcile hosts | Reissue every create as a new operation |
| Host-daemon restart, runtime alive | New service incarnation reconciles recorded resources | Trust a saved PID without ownership proof |
| Host reboot | Invalidate boot-bound capabilities; inspect actual runtime state | Pretend the old interactive process/PTY survived |
| Journal rollback with surviving runtime | Quarantine/account unmatched managed resources before new admission | Assume a valid older journal proves no newer work exists |
| smux owner lost | Report terminal uncertainty/loss; recover only supported state | Reconstruct a live PTY from transcript alone |
| Client disconnect | Detach client and preserve workload per policy | Implicit cancellation/destruction |
| Queued session cancelled while placement races | Preserve cancellation intent; abort or stop/reap the exact attempt | Publish a late ready session that becomes orphaned |
| Cancellation accepted | Keep stop/reap pending until evidence | Release GPU immediately |
| Full journal/disk | Stop new mutations, preserve evidence and report blocked | Execute unjournaled work or erase the old journal |
| Response publication fails | Retain request/result for reconciliation | Delete request regardless |
| Unsupported limit/device | Reject or choose a separately authorized supported plan | Claim enforcement that the provider cannot perform |
| Dirty worktree/failed agent | Retain and expose recovery actions | Delete it because a parent CLI exited |
| Partial destroy | Retry exact outstanding cleanup steps | Global prune or report fully removed |
| Prepared reservation expires before execute arrives | Reject late authorization; retain or reconcile any already-consumed intent | Launch using an authentic but expired receipt |
| Work exits but workspace is retained | Release proven compute only; retain storage/endpoint charges | Mark every resource free at process exit |

### 14.3 At-most-one acceptance versus physical execution

Controller fences can prevent an old result from being accepted and prevent cooperative hosts from accepting stale commands. They cannot by themselves stop arbitrary code already running on a partitioned machine.

For non-replay-safe work, allow replacement only after native termination/absence proof or an approved external fencing mechanism. Otherwise keep it pending/unknown and ask for an explicit recovery decision. Use per-attempt isolated workspaces and scoped credentials to reduce accidental conflict, but do not call that exactly-once execution.

Automatic retries need a policy class:

- Read-only/replay-safe: bounded retry under a new attempt after allowed reconciliation.
- Idempotent external action: use the external system's own idempotency key.
- Mutable interactive agent: resume the verified existing session or require a reviewed new attempt.
- Non-idempotent external action: no automatic replay after an unknown outcome.

## 15. Security, workspace, and artifact policy

### 15.1 Authority chain

Authenticate Caret/client to orchestrator, orchestrator to host, and attachment client to smux. Authorize each operation for project/namespace, workload, attempt and action. Schema validation and a matching digest are necessary integrity checks, not authentication.

Use cryptographic digests for immutable plan/evidence identity and authenticated channels/grants for authority. Fast hashes such as XXH3 may still accelerate local cache lookups but must not become an authorization token or sole adversarial integrity check.

No agent receives the host runtime socket, controller admin credential, unrestricted Docker named pipe, host home directory or an unrelated user's credential store. Required credentials are narrowly scoped references with explicit injection, logging and cleanup policy.

### 15.2 Workspace lifecycle

Each attempt gets an exact workspace ID and allowed root. Record repository/revision, owner, worktree/native path and creation operation. Use path containment and no-follow validation; labels or user-provided names alone do not prove ownership.

Default behavior:

- Detach or Caret crash: retain active workspace and session.
- Agent failure or host recovery: retain workspace/evidence.
- Explicit Terminate session: stop the workload, then evaluate retention separately. Closing a pane still means detach.
- Dirty/unpublished work: retain and warn; deletion requires explicit authorization.
- Clean, fully published ephemeral workspace: eligible for policy-driven exact cleanup.

Do not run broad worktree cleanup when any agent exits. Track parent/child associations, but a parent's disappearance is not proof all children or data are disposable.

### 15.3 Shared caches and artifacts

Use immutable content-addressed input/artifact sets where the existing cache/SCV architecture supports them. Give containers read-only cache access by default and private writable staging. The parent or designated cache publication owner validates and publishes accepted output.

Cache keys bind relevant source, compiler/toolchain, target OS/architecture/ABI, configuration and policy versions. A Linux host cross-compiling a Windows binary is still executing a Linux workload; do not confuse output target with execution OS.

Artifact upload/download is bounded and digest-verified. External runtime APIs may use JSON at the adapter boundary; persistent user configuration and native manifests remain SDN. Do not embed executable hooks into resource files as an implicit provisioning mechanism.

## 16. Observability and performance design

### 16.1 Correlation and diagnostics

Carry the following correlation chain through status/logs/traces:

`resource UID -> plan digest -> assignment/grant -> attempt -> operation -> native runtime -> smux session/generation -> accepted result`.

Expose queue reason, requested/effective resources, last confirmed liveness, uncertain ownership, provider capabilities, journal status, cleanup pending and workspace retention. “No output yet” and “unable to capture output” are different states.

Support structured SDN event export and bounded human-readable CLI views. Integrate existing Simple logging/AOP/XRay plans for optional detailed profiling, without making profiling a requirement for correctness or putting secrets into traces.

### 16.2 Bounded operation

Proposed initial engineering limits, to be measured and made configurable:

- Control frames: maximum 1 MiB decoded payload, bounded nesting/collection counts.
- Terminal stream chunks: maximum 64 KiB per frame; per-session replay budget initially 8 MiB, with explicit gaps after eviction.
- Separate bounded queues for control, cancellation, terminal output and artifact transfer so output floods cannot starve control.
- Streaming artifact transfer with declared size/digest and quota; never buffer a whole repository in a control message.
- Event-driven watches plus bounded reconciliation batches; no repeated full-directory scans per heartbeat.
- Cache static provider metadata by image digest/runtime version/generation; recheck mutation authority every time.
- Single-writer event application per authority; bounded worker/fiber pools for effects. Do not hold a global lock while pulling an image or waiting for a process.

These are design starting points, not measurements. Tune them using realistic code-agent output, large compile logs and failure storms.

### 16.3 Qualification targets

| Metric | Required evidence |
| --- | --- |
| Idle overhead | CPU/wakeups and RSS for daemon + smux, separately from runtime/workload |
| Control latency | p50/p95/p99 submit/status/cancel/resize, with and without output flood |
| Scheduling | Time and allocation correctness for 3,000 queued/recorded tasks across a representative fleet |
| Active concurrency | Separate measured limit for real running containers and attached terminals; do not equate it to 3,000 queued tasks |
| Recovery | Replay and reconciliation time versus active/retained operations, including checkpoints |
| Provider overhead | Warm/cold create/start/exec/stop/destroy, image pull excluded and included separately |
| Build/test regression | Baseline local throughput, warm startup, memory and accepted-result correctness |
| Memory growth | Bounded history/queues and long-duration create/finish cycles without per-attempt leaks |
| GPU scheduling | Device exclusivity, sharing semantics and no stale-grant reuse under cancellation/partition |

Set numerical release budgets after recording the baseline on designated hardware; report regressions with the same workload/configuration. Do not introduce mandatory heavy diagnostic checks into every production terminal event.

## 17. File-by-file implementation/refactoring map

Paths in the “existing” column are inspected repository targets. New module names below are proposed: use the established package layout and public export conventions, and check for overlapping implementations before creating a file.

| Work package | Existing targets | Planned change / proposed new target |
| --- | --- | --- |
| Strict schema registry | `common/contracts/orchestration/resource_v1.spl`, `ci_v1.spl` | Extract value-based decode helpers; add versioned resource-set/profile/session/host schema modules, preserving old entrypoints |
| Generic operation control | `common/contracts/distributed_control_v2.spl`, `distributed_control_codec_v2.spl`, `distributed_operation_state_v2.spl` | Reuse envelopes/transitions; add only missing workload/grant values and authorization integration |
| Operation storage | `common/task_runner/distributed_operation_journal_v2.spl` | Durability capability, checkpoints/compaction, retained-outcome/dedupe horizon and corruption handling |
| Task storage | `common/task_runner/contracts.spl`, `journal.spl` | Preserve build/test V1 and ownership; share lower-level storage mechanisms rather than widening domains |
| Daemon core | `nogc_sync_mut/daemon_sdk/{daemon,types,protocol,lock,client}.spl` | Correct publication/ack order, exact owner recovery, limits, versioning and compatibility wrappers |
| Async facade | `nogc_async_mut/daemon_sdk/` | Route to genuinely nonblocking dispatch/waits when enabled; do not duplicate the service engine |
| Service/process ownership | `nogc_sync_mut/service/daemon_base.spl`, `io/group_process_owner.spl` | Standardize owned lifecycle and exact cancel/reap adoption |
| Admission policy | `common/task_runner/fiber_scheduler.spl` and existing build admission | Preserve local policy; add a separate strict host-ledger implementation and pure admission tests |
| Container common | `common/contracts/container/runtime_v1.spl` and sibling capability/identity contracts | Add versioned lifecycle/stream/mount/env/device/stats values without weakening native isolation |
| Linux provider | `nogc_async_mut/container/providers/linux/oci_runtime_v1.spl` | Extend existing provider; qualify command semantics, Podman rootless, streams, limits and devices |
| Windows provider | Windows process-container architecture/design/test documents | Change first bridge to Docker; implement sibling `providers/windows/` leaf with the common contract |
| CI consumer | `app/ci/pipeline_runner.spl` | Keep existing real lifecycle; route through shared executor and add asynchronous/interactive capability where needed |
| Test consumers | `app/test_daemon/{main,light_daemon,generic_main,daemon}.spl`, `adapters/container_adapter.spl` | Converge entrypoints gradually; retain domain policies; remove shell/name-based lifecycle |
| Legacy test container | `nogc_sync_mut/test_runner/test_runner_container.spl` | Replace Docker-first version probing, shell command construction and global volume prune |
| Build integration | `app/buildrunner/{main,runner,database_session}.spl`, `app/build/scheduler/container_worker_admission.spl` | Shared executor mapping and a verified remote-evidence path; retain rejection until ready |
| Cache service | `app/cache_daemon/main.spl` and current service composition | Use common lifecycle/transport where beneficial, not host-owned cache publication |
| smux owner | `os/apps/smux/{server,api,core_mux_owner}.spl` | Finish framed typed dispatch, terminal transport attachment and exact mutation receipts |
| Mux contract/client | `common/contracts/mux/{port_v1,execution_v1,observation_v1}.spl`, `nogc_sync_mut/sosix/mux/{client_v1,config_v1}.spl` | Preserve base port/capture/receipt rules; add negotiated bind-existing/runtime identity and optional terminal stream extension |
| Caret convergence | `app/llm_caret/{pane_backend,agent_runtime,multi_caret_manager,agent_workspace,agent_plan}.spl` | One execution/session facade; provider-specific launch adapters; remove guessed fallback |
| Caret workbench | `workbench/{session_contract,session_source,distributed_composition}.spl` | Versioned native-process/runtime-execution union, workload/grant binding, per-attachment cursors, real provider/generation and actual composition |
| Host application | Existing orchestration host composition if present | Add the missing host-daemon executable/composition under the established app root; proposed name `orchestrator_host` |
| Controller application | Existing Simple Orchestrator modules/contracts | Complete service/store/scheduler/reconciler composition; do not create a competing orchestrator project |
| Developer tooling | Existing SDN LSP, CLI/MCP, requirements and SSpec indexes | Schema-driven diagnostics, explain/inspect commands, traceability and acceptance fixtures |

Before each change, rebase the implementation plan against the then-current revision. This report's pinned audit is not a guarantee that no later commit has already implemented part of a row.

## 18. Implementation phases and exit gates

### Phase 0 — Baseline and contracts

- Inventory actual entrypoints and record source/design/runtime qualification levels.
- Add architecture decisions for shared ownership, Docker-first Windows, explicit Apple VM lane and optional Kubernetes authority.
- Freeze existing decoder/CLI/local-runner behavior as regression fixtures.
- Define requirement IDs, schema defaults, supported provider subset and state/evidence mappings.

**Exit:** no ambiguous owner or conflicting engine selection; baseline tests identify existing behavior without claiming unexecuted cases passed.

### Phase 1 — Safety fixes in shared mechanisms

- Fix daemon response publication/acknowledgement.
- Replace failed-ping/PID-kill recovery with exact-instance ownership.
- Remove runtime-global prune and name-only destructive operations from affected adapters.
- Add bounded envelope decoding and immutable operation identity.

**Exit:** injected response failure, PID reuse, duplicate delivery and unrelated-resource cleanup tests pass. Existing local clients remain compatible.

### Phase 2 — Shared service and durable operation layer

- Compose owned service/process primitives with the existing distributed-operation journal.
- Add real bounded asynchronous dispatch, cancellation priority and timers.
- Add strict admission ledger, durability negotiation and checkpoint/compaction.
- Provide local IPC first; authenticated remote transport uses the same operation semantics.

**Exit:** restart at each mutation boundary preserves ownership/outcomes; a long workload cannot block health/cancel; no admission exceeds a hard budget.

### Phase 3 — Podman feature completion

- Extend the existing Linux provider and CI path rather than rewriting them.
- Add workspace/env/secret/exec/TTY/resize/stats/device capability support.
- Qualify command/entrypoint mapping, rootless enforcement and exact cleanup.

**Exit:** one real agent CLI can run in a Podman worktree container, be observed/cancelled, and leave unrelated containers/volumes untouched. Unsupported capabilities fail closed.

### Phase 4 — Host daemon and controller vertical slice

- Enrollment, capability refresh, desired-state store, placement, host confirmation and fenced execution.
- Min/recommend/prefer resolution and scarcity-aware scheduling.
- Recoverable assignment protocol, drain, inspect and explain commands.

**Exit:** two hosts run mixed eligible workloads without duplicate attempts or over-allocation; network partition leaves unsafe retries blocked.

### Phase 5 — smux and Caret end-to-end

- Complete typed mux owner/client route and orchestrated-session adapter.
- Add the versioned runtime-execution binding and authenticated bind-existing operation, without reusing V2's PID identity for an exec helper.
- Replace divergent Caret launch routes and hardcoded identities.
- Add real provider adapters, attach/reconnect and separate control actions.

**Exit:** Caret requests SDN template + task, receives an effective placement, attaches to chosen agent, detaches/reconnects, and explicitly uses Terminate session with correct workspace retention. Host-daemon restart, expired mux receipt recovery, and cancellation racing placement cannot duplicate/orphan the agent or falsely claim stream continuity.

### Phase 6 — Build/test/CI migration

- Migrate daemon entrypoints and legacy container consumers incrementally.
- Add verified remote evidence while preserving parent result/cache authority.
- Keep fast local mode and domain scheduler behavior.

**Exit:** local behavior/performance stays within measured budgets; remote results are rejected unless fully bound and verified; no missing tests become passes.

### Phase 7 — Windows Docker hardening/qualification

Design and safety work starts alongside Phases 1–3; the production gate follows the common interfaces and terminal model.

- Implement canonical Windows provider, service/broker boundary and process-only enforcement.
- Run the exact Windows host/image/engine matrix, including the separately labeled Windows 11 development lane.
- Qualify terminal, cancellation, restart, resource enforcement and partial cleanup.

**Exit:** no fallback to other isolation/OS; exact identity and cleanup evidence; unsupported host/image/architecture is refused.

### Phase 8 — Optional backends and operational scale

- FreeBSD jail provider and privileged-broker qualification.
- Apple explicit Linux-VM provider, and optional installed-version-qualified Apple Kubernetes cluster adapter.
- Existing Kubernetes adapter with single resource authority.
- Stronger controller HA only after storage/leader fencing is designed and tested; not multiple controllers pointed at an arbitrary shared file directory.

**Exit:** each backend independently passes capability and failure tests. One backend's pass does not certify another.

## 19. Acceptance, integration, system, and formal checks

Use the repository's modern SSpec structure and requirement traceability. Each case links requirement → feature → acceptance → integration/unit evidence → implementation → bug/regression reference where applicable. Generate Markdown/HTML summaries from the same test inventory.

| Test ID | Level | Scenario and required assertion |
| --- | --- | --- |
| AT-CFG-01 | Acceptance/unit | IaC-only, orchestration-only and combined ResourceList resolve consistently |
| AT-CFG-02 | Unit/property | Duplicate keys, unknown fields, overflow, invalid ordering, cycles and bad references fail with correct spans |
| AT-CFG-03 | Integration | Existing Pod/Deployment/Job/Pipeline fixtures preserve semantics |
| AT-DAE-01 | Fault injection | Response publication fails after execution: request/outcome remains recoverable; no duplicate effect |
| AT-DAE-02 | System | Hung ping and recycled PID cannot kill an unrelated process |
| AT-DAE-03 | Model/integration | Same operation ID/same payload returns retained state; changed payload fails |
| AT-DAE-04 | Fault injection | Crash before/after journal commit, native effect, projection and response: no fabricated success |
| AT-DAE-05 | Storage | Checkpoint/compaction crash, expired dedupe horizon, corrupt tail and full disk preserve safe behavior |
| AT-HOST-01 | Integration/system | Claimed capability or image digest unsupported by live host is refused |
| AT-HOST-02 | Concurrency | Competing reservations cannot exceed memory budget or double-allocate an exclusive GPU |
| AT-HOST-03 | System | Restart/reboot/engine reconnect changes identity and rejects stale grants |
| AT-HOST-04 | Multi-user concurrency | Two rootless scopes cannot reserve the same physical GPU or overlapping machine memory budget |
| AT-HOST-05 | Fault injection | Expiry races execute authorization; lost prepare/commit replies and duplicate authorization never cause a late launch or double grant |
| AT-HOST-06 | Recovery/storage | Rolled-back journal plus surviving/restarted container blocks admission until reconciled; retained failed workspaces remain quota-charged |
| AT-ORCH-01 | Acceptance | Preferred resources unavailable: effective allocation stays above min and is explained |
| AT-ORCH-02 | Acceptance | Single exclusive GPU queues other exclusive tasks even with spare CPU/RAM |
| AT-ORCH-03 | System | Partitioned host is not presumed dead; unsafe replacement remains blocked |
| AT-CTR-01 | Real Podman | Workspace, env, secrets, working directory and command/entrypoint behavior match the typed request |
| AT-CTR-02 | Real provider | Effective hard limits are observed/enforced, not merely printed in configuration |
| AT-CTR-03 | Real provider | Exact cleanup preserves unrelated container, network, volume and dirty worktree |
| AT-CTR-04 | Real Windows | Wrong OS/image/isolation/engine fails; supported process pair succeeds with observed evidence |
| AT-CTR-05 | Real Podman/CLI | Chosen agent works with read-only rootfs and only declared private writable state/scratch; no host home mount is required |
| AT-MUX-01 | Integration/system | Lost create reply and duplicate reconnect do not launch a second terminal/agent |
| AT-MUX-02 | System | Client detach keeps workload alive; terminate is separate and exact |
| AT-MUX-03 | Concurrency | Input and geometry leases cannot be stolen by replay/stale revision |
| AT-MUX-04 | Stress | UTF-8 boundary, large output, replay gap and slow client do not starve cancel/control |
| AT-MUX-05 | System | Transport helper/host daemon restarts while smux/runtime remain alive; runtime execution identity stays correct and stream continuity/loss is honest |
| AT-MUX-06 | Concurrency | Two viewers at different event/capture/byte positions retain valid execution binding and independent control leases |
| AT-MUX-07 | Recovery | Lost create reply followed by lease expiry/history eviction yields only permitted receipt recovery or Unknown, never duplicate launch |
| AT-MUX-08 | Fault injection | Crash at runtime create/start/bind/ready boundaries recovers one agent and one binding |
| AT-CARET-01 | End-to-end | Template + task reaches chosen real CLI with correct status and no guessed provider flags |
| AT-CARET-02 | End-to-end | Resume unsupported/agent exited/owner lost is represented honestly |
| AT-CARET-03 | Race/acceptance | Cancel queued/reserved/preparing/ready-not-attached session; delayed placement cannot launch or leave an untracked agent |
| AT-CARET-04 | Action/authority | Supported and unsupported provider interrupt, build cancellation, history deletion and workspace deletion remain separately authorized |
| AT-RUN-01 | Integration | Remote evidence is rejected until verified path is selected and all identity/input/output checks pass |
| AT-RUN-02 | Integration | Missing test inventory, malformed result, reset failure or incomplete reap cannot be accepted as pass |
| AT-SEC-01 | Negative/system | Agent cannot access host engine socket, unrelated secret/workspace or unauthorized action |
| AT-OPS-01 | Recovery | Drain/update retains live ownership and incompatible versions fail without rewriting evidence |
| AT-EXT-01 | Platform system | Apple VM, FreeBSD jail and Kubernetes retain distinct OS/isolation/authority semantics |

### Formal/model-based scope

Model-check or prove the small transition/admission cores: immutable operation identity, allowed state transitions, monotonic assignment fences, no double exclusive reservation, no release-before-reap/absence proof, and parent-only result publication. Connect models to the actual versioned types and transition functions.

Proofs of an abstract state machine do not prove Docker, Podman, HCS, jail, filesystem flush or PTY behavior. Combine model/property tests with crash injection and real-system tests. Heavy verification can remain in inspection/CI builds; cheap boundary validation and ownership checks must remain in production.

### Test execution and reporting policy

- Use repository-approved self-hosted compiler/test entrypoints for implementation qualification, not a seed/compatibility runtime that cannot exercise the same system.
- Separate unit adapters from application code; do not introduce fake success in production paths.
- A test that was authored but not executed is `NOT_RUN`; unavailable platform fixtures are `BLOCKED`, not pass.
- Record source SHA, compiler/runtime/engine versions, host/image identity, commands, selected tests and evidence.
- Run targeted regressions for each work package and required cross-platform gates; do not repeat already-green expensive suites without a relevant change.
- All acceptance tests in this report are planned, not executed by this document task.

## 20. Rollout and rollback

1. Add versioned contracts and tests first; preserve old public entrypoints.
2. Introduce compatibility adapters and read-only shadow planning. Shadow mode may compare decisions but must not perform a second set of effects.
3. Migrate one local test/CI path to shared mechanisms; observe safety and performance.
4. Enable one dedicated Podman development host, then a small multi-host pool.
5. Enable orchestrated Caret behind an explicit execution-target choice.
6. Enable remote build/test evidence only after its acceptance gate.
7. Roll out Windows and later backends independently.
8. Remove legacy routes only after all callers are migrated and compatibility policy permits removal.

Flags should select a complete owner/adapter path, not mix half of an old lifecycle with half of a new one. Persist the selected backend/contract versions in attempt evidence.

Rollback stops new admission, drains or preserves active work according to policy, and returns future requests to the prior qualified adapter. Never let an old binary rewrite a newer journal or independently relaunch surviving attempts. If downgrade cannot read retained state, keep the newer recovery service available until work is settled.

## 21. Difficulty, effort, and principal risks

### 21.1 Engineering difficulty

These are planning estimates, not measured delivery commitments. Assumptions: experienced Simple contributors, access to real Linux/Windows fixtures, existing libraries build, and no large unrelated compiler/runtime blockers. One person-week means focused engineering effort; calendar time depends on parallelism and qualification availability.

| Package | Difficulty | Indicative person-weeks | Main uncertainty |
| --- | --- | --- | --- |
| SDN schema/dispatch and profiles | Medium | 1–3 | Existing decoder boundaries and compatibility fixtures |
| Shared daemon correctness/refactor | High | 3–6 | Ownership migration, asynchronous effects and recovery behavior |
| Journal checkpoints/durability | High | 2–5 | Storage flush guarantees and crash-safe compaction |
| Podman missing features/conformance | Medium–high | 2–5 | Rootless limits, command semantics and terminal streams |
| Host service + native scheduling | High | 4–8 | Fencing, local/global reservation reconciliation and restart |
| smux/Caret convergence | High | 3–6 | Existing divergent launch routes and terminal-owner continuity |
| Build/test remote evidence integration | High | 2–5 | Parent authority, result completeness and domain regressions |
| Windows canonical Docker provider | High | 3–7 | Host/image matrix, permissions, terminal and partial cleanup |
| Each optional backend | Medium–high to high | 2–6 | Actual platform capability and failure qualification |

Ranges overlap and should not be added into a promised calendar schedule. A narrow two-host Podman prototype is materially smaller than a production-qualified four-OS system. The difficult part is not invoking a container CLI; it is keeping ownership, resource accounting, interactive state and accepted results correct under failure.

### 21.2 Risk register

| Risk | Severity | Mitigation / release gate |
| --- | --- | --- |
| Duplicate external effects after lost response | Critical | Journaled immutable operation, retained outcome, unknown-state reconciliation |
| Global prune or reused-PID kill | Critical | Remove broad cleanup; exact owned identity and evidence |
| Split-brain host execution | Critical | Fenced authority, preserve uncertain grants, no unsafe automatic replacement |
| False memory/GPU guarantees | High | Strict ledger, provider enforcement proof, explicit sharing mode |
| Privileged runtime access leaks to agent | Critical | Narrow broker, private engine socket, scoped credentials |
| Terminal has multiple owners/readers | High | CoreMux boundary and one exclusive terminal stream owner |
| Shared daemon rewrite breaks fast local build/test | High | Compatibility facade, domain-preserving migration and local baseline |
| Journal exhausted or falsely power-loss safe | High | Compaction, dedupe retention, explicit tested durability profile |
| Unsupported Windows/Apple/jail semantics masked | High | Capability-driven fail-closed admission and separate platform gates |
| Remote output poisons trusted cache | Critical | Parent-verified input/toolchain/output/evidence and controlled publication |
| Scope expands into a full Kubernetes clone | High | Narrow first feature set; optional existing Kubernetes adapter |

## 22. Definition of done

The first complete release is done when:

1. Caret creates a local or orchestrated session through one user-facing model and receives honest status.
2. One SDN format handles configuration-only, workloads-only and combined resources, with strict versioned validation.
3. A real host registers usable capabilities and the orchestrator assigns only feasible, authorized resources.
4. The host safely confirms reservations and executes through the existing improved Container providers.
5. Podman supports workspace-backed interactive agents; Windows Docker process isolation passes its independent qualification gate.
6. smux is the sole terminal authority, with detach/reconnect, bounded replay and separate control leases/actions.
7. Shared daemon/journal/process code is actually consumed by the host and migrated runner paths, without merging their domain authority.
8. Response loss, crash, PID reuse, partition, full disk, stale grant and partial cleanup do not cause duplicate mutation, false success or deletion of unrelated data.
9. Build/test parents retain their result/cache-publication rules and reject unverified remote evidence.
10. Runtime evidence, tests and limitations are recorded; unsupported platforms or features remain visibly blocked.

**Bottom line:** improve the existing daemon and distributed-control foundation; compose a host execution service from it; keep Simple Container as the local runtime layer; keep Simple Orchestrator as the placement/desired-state owner; and converge Caret on the existing typed smux terminal contract. This gives one coherent distributed agent system without duplicating four different supervisors or forcing every backend to pretend it is the same kind of container.

## Appendix A. Pinned repository evidence

All S-links refer to `3ef23d69caa361369603a761f114c5613f7ea7b7`. Line anchors are supplied for source inspection, not as claims of executed tests.

- **S01:** [Strict orchestration resources](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/contracts/orchestration/resource_v1.spl) — resource model, decoder and source-span rejection.
- **S02:** [CI Job/Pipeline contracts](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/contracts/orchestration/ci_v1.spl).
- **S03:** [Container runtime contract](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/contracts/container/runtime_v1.spl) — exact values and probe-only portable trait.
- **S04:** [Linux OCI runtime provider](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/nogc_async_mut/container/providers/linux/oci_runtime_v1.spl) — lifecycle, recovery, unavailable stats and command builder.
- **S05:** [CI pipeline container execution](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/ci/pipeline_runner.spl#L292) — real lifecycle wiring.
- **S06:** [Build/container admission](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/build/scheduler/container_worker_admission.spl).
- **S07:** [Windows process-container architecture](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/doc/04_architecture/windows_server_process_container.md) — proposed provider and historical containerd/runhcs choice.
- **S08:** [Legacy test-container helpers](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/nogc_sync_mut/test_runner/test_runner_container.spl) — runtime detection, shell operations and global volume cleanup.
- **S09:** [Daemon SDK loop](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/nogc_sync_mut/daemon_sdk/daemon.spl#L46).
- **S10:** [Daemon SDK client recovery](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/nogc_sync_mut/daemon_sdk/client.spl#L42).
- **S11:** [Owned daemon service lifecycle](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/nogc_sync_mut/service/daemon_base.spl#L63).
- **S12:** [Group process owner](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/nogc_sync_mut/io/group_process_owner.spl).
- **S13:** [Task-runner identity/evidence contracts](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/task_runner/contracts.spl).
- **S14:** [Task-runner journal](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/task_runner/journal.spl).
- **S15:** [Distributed-operation journal V2](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/task_runner/distributed_operation_journal_v2.spl).
- **S16:** [Distributed-control V2](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/contracts/distributed_control_v2.spl) and [codec](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/contracts/distributed_control_codec_v2.spl).
- **S17:** [Distributed-operation state V2](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/contracts/distributed_operation_state_v2.spl).
- **S18:** [Local fiber scheduler](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/task_runner/fiber_scheduler.spl#L126) — domain-specific progress overcommit.
- **S19:** [Test-daemon CLI](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/test_daemon/main.spl) and [light daemon](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/test_daemon/light_daemon.spl).
- **S20:** [Generic test-daemon entrypoint](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/test_daemon/generic_main.spl) and [SDK daemon composition](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/test_daemon/daemon.spl).
- **S21:** [Test-daemon container adapter](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/test_daemon/adapters/container_adapter.spl).
- **S22:** [BuildRunner entrypoint](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/buildrunner/main.spl) and [runner exports](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/buildrunner/runner.spl).
- **S23:** [BuildRunner database session](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/buildrunner/database_session.spl) — explicit remote-evidence rejection.
- **S24:** [Cache-daemon entrypoint](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/cache_daemon/main.spl).
- **S25:** [CoreMux port](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/contracts/mux/port_v1.spl) and [execution contracts](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/contracts/mux/execution_v1.spl).
- **S26:** [smux server](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/os/apps/smux/server.spl) and [API](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/os/apps/smux/api.spl).
- **S27:** [CoreMux owner](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/os/apps/smux/core_mux_owner.spl).
- **S28:** [Mux client](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/nogc_sync_mut/sosix/mux/client_v1.spl) and [loopback configuration](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/nogc_sync_mut/sosix/mux/config_v1.spl).
- **S29:** [Caret mux wire design/status](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/doc/05_design/caret_mux_wire_sosix_v1.md).
- **S30:** [Caret pane backend](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/llm_caret/pane_backend.spl) and [agent runtime](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/llm_caret/agent_runtime.spl).
- **S31:** [Multi-Caret manager](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/llm_caret/multi_caret_manager.spl) and [agent workspace](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/llm_caret/agent_workspace.spl).
- **S32:** [Agent launch planning](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/llm_caret/agent_plan.spl).
- **S33:** [Session binding/control V2](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/llm_caret/workbench/session_contract.spl#L158).
- **S34:** [Session source projection](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/llm_caret/workbench/session_source.spl).
- **S35:** [Distributed workbench composition descriptors](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/app/llm_caret/workbench/distributed_composition.spl).
- **S36:** [Mux observation, capture and receipt semantics](https://github.com/ormastes/simple/blob/3ef23d69caa361369603a761f114c5613f7ea7b7/src/lib/common/contracts/mux/observation_v1.spl).

## Appendix B. Official platform references

Platform behavior is version-sensitive. These sources support the platform boundaries; the proposed Simple architecture, schemas, defaults, estimates and tests are design recommendations, not claims made by those projects.

- **W01:** [Podman system service and security](https://docs.podman.io/en/latest/markdown/podman-system-service.1.html).
- **W02:** [Microsoft: Windows container version compatibility](https://learn.microsoft.com/en-us/virtualization/windowscontainers/deploy-containers/version-compatibility).
- **W03:** [Microsoft: Windows container isolation modes](https://learn.microsoft.com/en-us/virtualization/windowscontainers/manage-containers/hyperv-container).
- **W04:** [Microsoft: Windows container support policy](https://learn.microsoft.com/en-us/troubleshoot/windows-server/containers/support-for-windows-containers-docker-on-premises-scenarios) and [resource controls](https://learn.microsoft.com/en-us/virtualization/windowscontainers/manage-containers/resource-controls).
- **W05:** [NVIDIA: GPU time slicing versus MIG](https://docs.nvidia.com/datacenter/cloud-native/gpu-operator/latest/gpu-sharing.html).
- **W06:** [FreeBSD Handbook: Jails and Containers](https://docs.freebsd.org/en/books/handbook/jails/).
- **W07:** [Apple official container repository and requirements](https://github.com/apple/container).
- **W08:** [Kubernetes: Windows support](https://kubernetes.io/docs/concepts/windows/) and [Windows container limitations](https://kubernetes.io/docs/concepts/windows/intro/).
- **W09:** [Apple container current-branch command reference](https://github.com/apple/container/blob/main/docs/command-reference.md) — experimental cluster management; verify the installed release rather than assuming current-branch features are released.
- **W10:** [Kubernetes: force deletion and duplicate-identity risks](https://kubernetes.io/docs/tasks/run-application/force-delete-stateful-set-pod/).
- **W11:** [Kubernetes: node status and heartbeats](https://kubernetes.io/docs/reference/node/node-status/).
- **W12:** [Podman run: CPU quotas, cgroups and resource options](https://docs.podman.io/en/latest/markdown/podman-run.1.html).
