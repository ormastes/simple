<!-- codex-research -->

# SimpleOS Enhancement Assessment

## Assessment

**SimpleOS supports service concepts, but it does not yet have a production-grade service subsystem.** It currently has:

1. boot-time routines that initialize storage, networking, display, and an inline HTTP server;
2. a generic `InitService` dependency/restart model;
3. a typed `ServiceManifest` lifecycle model;
4. a specialized driver supervisor and grant broker.

The actual boot path still initializes many “services” synchronously inside the kernel, probes the root filesystem, and then runs an inline HTTP server or serial shell. Despite the header describing an init launch, `os_main()` does not start a real PID 1 userspace process.

The generic `InitService` already models dependencies, capabilities, priorities, restart policies, crashes, and quarantine, but I found no production call site; the indexed references are specifications and unit tests.

`ServiceManifest` is a stronger declarative model with readiness dependencies, watchdogs, health state, bounded restart, and the important rule that a restarted service receives no stale grants. However, the repository’s own lane status describes this as model/spec-complete and lists live supervisor wiring and QEMU crash/restart evidence as future work.

Therefore:

> **SimpleOS has service-management components, but it does not yet have a single, live, userspace service manager that owns process creation, supervision, authority, resource control, and shutdown.**

That service manager should be the next architectural center of SimpleOS.

---

## 1. Current maturity by subsystem

| Subsystem | Current state | Production verdict |
| --- | --- | --- |
| Boot services | Synchronous kernel initialization and hardware probes | Useful bring-up code, not managed services |
| Generic service manager | Dependency, ordering, restart, quarantine model | Apparently unit-test-only |
| Typed service manifest | Readiness, health, watchdog, restart, grant clearing | Good contract, not live orchestration |
| Driver supervisor | Device health, restart, release/re-grant logic | Reusable specialized runtime |
| Process scheduler | TCB has address space, capabilities, parent, scheduling and basic isolation metadata | Substantial foundation, incompletely connected to boot and every spawn path |
| Capability system | Typed capabilities, lineage, generation, delegation depth and attenuation | Strong model, partial live enforcement |
| LLM profiles | Role/profile intersection and spawn adapter | Partial adapter, several authority classes unmapped |
| Container manager | Lifecycle, namespace, resources, image, restart and storage models | Mostly pure model |
| Container isolation | Root-path and PID-view model; one VFS path family partially wired | Not Docker-equivalent |
| OCI support | Validates normalized OCI-like inputs, digests and unsafe settings | No live registry pull, unpack or runtime |
| Container storage | Layer/COW/volume/GC bookkeeping | No real VFS-backed storage or power-fail evidence |

The scheduler’s task record already carries a `CapabilitySet`, address space, parent and `TaskIsolationProfile`, but the isolation profile is currently a small collection of flags and limits rather than a complete namespace/resource/security context.

There is also an explicitly tracked architectural gap in the filesystem-exec path: it cannot resolve a scalar caller ID to the caller’s real `TaskControlBlock.capabilities`, while other spawn syscalls use a live scheduler path. This is evidence that authority checks are fragmented across process-creation implementations.

---

## 2. Missing parts before SimpleOS is a general-purpose OS

The repository’s production-status ledger and missing-subsystem audit consistently describe many pieces as partial, model-only, or not connected to boot.

### P0: End-to-end process and service operation

These are the immediate blockers:

* Boot a filesystem-backed ring-3 init process.
* Use one live scheduler instance for all process creation.
* Give every syscall a trustworthy caller `TaskId` and execution context.
* Complete process exit, parent notification, wait/reap and orphan adoption.
* Run drivers, VFS, network and other services as supervised processes rather than inline kernel functions.
* Make timer preemption and context switching part of the normal booted runtime.
* Produce QEMU evidence that two independent userspace services run, communicate, crash, restart and retain isolation.

Until these work together, higher-level container and agent policy cannot be considered enforced.

### P1: Core operating-system facilities

#### Memory and executable ABI

SimpleOS needs a consistently live implementation of:

* anonymous and file-backed mappings;
* shared mappings;
* copy-on-write fork or a deliberately non-fork process model;
* page-fault handling and demand paging;
* guard pages and stack growth policy;
* executable and non-executable mappings;
* dynamic linking or an explicitly static application ABI;
* reliable user-pointer copying on every syscall;
* memory accounting per process and job.

#### Filesystem and storage

It needs:

* all VFS operations routed through the same caller-aware path;
* file-descriptor-level authorization after open;
* safe symlink, rename, mount and path traversal semantics;
* writeback, synchronization, crash recovery and filesystem checking;
* durable metadata transactions;
* mount lifecycle and unmount ordering;
* per-user and per-container ownership/quotas;
* persistent logs and core dumps.

#### IPC and synchronization

It needs production paths for:

* endpoint/channel objects;
* capability transfer;
* signals and process notifications;
* futex or equivalent thread synchronization;
* polling and event multiplexing;
* local stream/datagram IPC;
* shared-memory grants with revocation;
* endpoint lifecycle and peer-death notification.

#### Networking

It needs:

* application socket syscalls connected to the live network stack;
* DNS/resolver service;
* routing and interface configuration;
* per-process and per-container network policy;
* egress filtering;
* loopback and virtual interfaces;
* connection accounting and rate limiting;
* network namespace or equivalent per-isolation-domain network view.

#### Device operation

It needs:

* complete IRQ delivery and acknowledgement;
* DMA and IOMMU enforcement;
* device hotplug and removal;
* service restart after driver failure;
* cancellation of outstanding requests;
* power-management paths;
* device access mediated through typed handles rather than global driver calls.

### P2: General interactive/server OS facilities

These can follow the P0/P1 enforcement foundation:

* users, groups, login sessions and credential storage;
* per-user service managers;
* terminal/job control;
* complete POSIX compatibility;
* package and system-image updates;
* rollback and recovery mode;
* time synchronization and secure random initialization;
* desktop session and GUI service management;
* observability, tracing, crash reports and administrative APIs.

POSIX UID/GID should be supported for compatibility, but it should not become the primary SimpleOS authority mechanism.

---

## 3. One consistent security architecture

SimpleOS should **not** add separate security systems for humans, services, LLMs, agents and containers. They should all compile into one execution-security model.

The recommended rule is:

> **Roles and profiles are the policy control plane. Typed object capabilities are the runtime enforcement plane.**

A kernel syscall should never ask, “Does this process have role `agent_admin`?” It should ask, “Does this process hold a live handle with the exact required right?”

This follows the capability-space approach used by seL4, where each thread has a CSpace and different capabilities to the same object may carry different rights, and Fuchsia’s handle model, where rights can be reduced and process creation depends on possession of a job handle. [seL4 Documentation][1] [Fuchsia][2] [Fuchsia][3]

### 3.1 Unified principal hierarchy

Introduce a common `PrincipalId` for:

* human account;
* login session;
* system service;
* user service;
* local model service;
* remote model endpoint;
* agent controller;
* agent instance;
* subagent instance;
* tool broker;
* container or pod;
* scheduled job.

A normal hierarchy would be:

```text
RootJob / PID1
├── system-services
├── device-services
├── containers
└── user-session:<user>
    ├── interactive-apps
    └── agent-controller
        ├── agent:<task-id>
        │   ├── subagent:<test>
        │   └── subagent:<research>
        └── agent:<other-task>
```

Each node has its own:

* identity;
* job/lifetime object;
* CSpace or handle table;
* isolation domain;
* resource domain;
* audit context;
* parent delegation relationship.

Closing or revoking a job should recursively terminate its processes and revoke authority delegated from it.

### 3.2 Identity is not authority

A workload identity proves **who the process is**. It should not itself be a long-lived collection of permissions.

Use a short-lived, process-bound workload identity for authenticated IPC and network communication, similar to SPIFFE’s short-lived SVID and workload API model. Authorization should remain in current capabilities and broker policy, so permissions can be changed or revoked without waiting for an identity certificate to expire. [SPIFFE][4]

For SimpleOS:

```text
identity:
    principal_id
    tenant_id
    image_hash
    signer
    role_version
    parent_principal
    session_id
    issued_at
    expires_at
```

Authority remains separately represented by object handles and rights.

### 3.3 Replace ambient authority

One important existing problem is the representation of full authority:

* `CapabilitySet.full()` returns an unpledged set with zero tokens;
* `CapabilitySet.has()` interprets that empty-looking set as allow-all;
* least-authority minting requires concrete parent tokens, so ambient full authority cannot provide proper derivation lineage.

Replace this with a non-transferable kernel object:

```text
RootMintAuthority
```

Only PID1 initially receives this object. It is not an ordinary `CapabilitySet`, cannot be sent to another process, and can mint root capabilities only according to verified system policy.

After PID1 is running:

* turn ambient-spawn sealing on;
* reject all `CapabilitySet.full()` use;
* require a concrete parent capability for every delegation;
* make an empty CSpace always deny all operations.

The current boot code deliberately leaves the ambient seal off, and the production ledger lists root-capability seeding and QEMU proof as the remaining conditions before enabling it.

### 3.4 Effective authority at spawn

The existing `spawn_authority` direction is correct. Generalize it for every workload:

```text
effective_authority =
      parent_delegable_authority
  ∩   system_ceiling
  ∩   tenant_ceiling
  ∩   human_or_session_delegation
  ∩   role_profile
  ∩   executable_image_ceiling
  ∩   manifest_request
  ∩   runtime_context_constraints
  −   explicit_denials
```

The requested role is only a request. A process cannot self-assign a role, and a parent cannot give a child authority that it does not possess or is not allowed to delegate.

The repository already has most of this intersection logic, content-addressed image association, monotonic attenuation, delegation depth, token lineage, revocation generation and single-use capability support. The missing part is consistent injection into every live spawn, fork and exec path.

### 3.5 Five enforcement planes

Every role or workload profile should compile to these five outputs:

#### 1. Object authority

What objects may be used:

* directory/file handles;
* IPC endpoints;
* process/job handles;
* sockets or network routes;
* devices and IOMMU domains;
* datasets;
* secrets brokers;
* model brokers;
* UI/input services.

#### 2. Namespace and view isolation

What the process can see:

* filesystem and mount view;
* process view;
* IPC endpoint namespace;
* network stack or egress view;
* device namespace;
* hostname/time view where needed.

#### 3. Syscall attack-surface restriction

Which kernel calls can be attempted.

This is analogous to seccomp’s attack-surface reduction, but it must remain a restriction layer rather than a complete authorization system. Linux explicitly documents that seccomp filtering is not by itself a sandbox. [Kernel.org][5]

#### 4. Resource and lifetime control

What the process hierarchy can consume:

* CPU time and CPU placement;
* memory and mapped pages;
* process/thread count;
* storage and I/O bandwidth;
* network bandwidth;
* open handles;
* wall-clock time;
* model tokens and monetary budget;
* tool-call count.

Resource budgets must be hierarchical: a child may consume only a subset of its parent’s remaining budget. Linux cgroup v2 uses a comparable hierarchical controller model for CPU, memory, I/O and process limits. [OCI runtime specification][6]

#### 5. Identity, audit and approval

Who initiated the action, through which delegation chain, using which image, role, model, input and approval.

These planes only restrict each other. A syscall filter, namespace flag or role string must never grant access absent an object capability.

---

## 4. Capability types that need improvement

The current `CapabilityKind` already covers files, network ports, process spawn/signal, hardware, storage, IPC, VM and system operations.

It should be hardened as follows.

### Filesystem

Current path-prefix capabilities are useful for manifests but should not be the final kernel object.

Use:

```text
DirectoryHandle:
    vnode_id
    mount_generation
    rights
    subtree_allowed
```

The service manager resolves a manifest path once and passes a directory handle. All later access is relative to that handle. This avoids policy ambiguity caused by rename, symlink and mount changes. Fuchsia directory capabilities similarly route concrete directories with rights that can only be reduced along the route. [Fuchsia][7]

### Process authority

Replace numeric-target capabilities where possible:

```text
ProcessHandle(process_id, generation, rights)
JobHandle(job_id, generation, rights)
```

Rights should distinguish:

* inspect;
* wait;
* signal;
* terminate;
* debug;
* create child;
* delegate child authority.

Generation prevents PID reuse from retargeting an old capability.

### IPC

Replace text-only service names with endpoint handles:

```text
EndpointHandle(endpoint_id, generation, connect|listen|send|receive)
```

A component/service manager may resolve a human-readable service name, but the kernel should enforce the endpoint object.

### Network

`NetConnect(port)` is too coarse. Add:

```text
NetConnect:
    protocol
    address_or_route_id
    port_range
    byte_budget
    expiry

NetListen:
    protocol
    local_interface
    port
```

Domain-name access should normally go through an egress broker so DNS rebinding and mutable addresses cannot silently widen policy.

### Secrets

An agent should almost never receive a raw secret.

Add:

```text
SecretUse:
    secret_id
    permitted_operation
    target_service
    expiry
    max_uses
```

For example, a GitHub agent receives access to `git.push(repository, branch)` through a broker. It does not receive a personal access token.

### Model and agent-specific capabilities

Add:

```text
ModelInfer(model_id, data_class, token_budget)
ToolInvoke(tool_id, operation_set)
AgentSpawn(allowed_child_profile, max_depth)
DatasetRead(dataset_id, classification)
MemoryRead(memory_space_id, scope)
UiCapture(surface_id)
UiInput(surface_id)
ClipboardRead
ClipboardWrite
```

The current LLM profile adapter maps only part of the profile surface and deliberately fails closed for network, process-spawn, secrets, UI and model rights because corresponding kernel/broker authorities are not yet available.

---

## 5. Human, LLM and agent role model

### Human account

A human account gets a long-lived identity and a policy ceiling, but no running authority by itself.

At login, create a short-lived session:

```text
HumanAccount
    └── LoginSession
        ├── session CSpace
        ├── session resource budget
        ├── session job
        └── approval capability
```

Administrator status should mean the user may request or approve privileged operations. It should not mean every application launched by that user automatically receives administrative authority.

### LLM model service

Treat the model separately from the agent:

* a local model server is a service with model weights and accelerator access;
* a remote provider is accessed through a model broker;
* the agent receives `ModelInfer`, not the provider API key;
* the broker enforces model selection, token limits, data classification and audit;
* model output has no special authority.

### Agent controller

The controller may:

* create an agent instance;
* select an allowed profile;
* provide task input;
* assign a bounded budget;
* revoke or terminate the agent;
* receive its output.

It should not automatically inherit all authority of the human session.

### Agent instance

Each agent instance should have its own process or job, even when the same binary is reused. The existing SimpleOS CSpace design already intends to support the same immutable image with different per-instance capability pouches.

An agent profile could be represented in existing Simple SDL rather than introducing a new policy language:

```text
agent_role code_worker:
    image:
        hash: "blake3:..."

    authority:
        fs_read:
            - workspace
        fs_write:
            - workspace.src
            - workspace.test

        ipc_connect:
            - model.broker
            - git.read
            - test.runner

        child_roles:
            - test_worker

        deny:
            - secret.raw
            - net.raw
            - device.any
            - system.mount
            - system.policy_modify

    isolation:
        filesystem: workspace_snapshot
        process: private
        ipc: private
        network: broker_only
        syscall_profile: agent_compute

    resources:
        cpu: 2
        memory_bytes: 2147483648
        pids: 16
        wall_time_seconds: 1800
        model_tokens: 200000
        tool_calls: 1000

    approval:
        git_push: exact_transaction
        deploy_production: human
        permanent_delete: human
```

This manifest is compiled by the trusted policy service. The agent cannot edit or reinterpret it.

### Subagents

A subagent must receive a strict subset of its parent’s delegable rights:

```text
parent agent:
    read/write source
    run tests
    inspect git
    request push approval

test subagent:
    read source snapshot
    execute test runner
    write only test artifacts
    no git write
    no secrets
    no general network
```

The parent should pass object handles, not paths or credentials.

### High-impact operations

Destructive and externally visible operations should use narrow, one-shot approval grants:

```text
ApprovalGrant:
    requesting_principal
    operation
    target_object
    arguments_hash
    proposed_diff_hash
    maximum_effect
    expires_at
    nonce
    single_use
    approver_identity
```

The trusted approval service—not the LLM—renders the confirmation UI from the canonical transaction. This matters because agent-generated approval text itself can be deceptive. OWASP guidance recommends action-level least privilege, separate minimal credentials, dry-run or reversible transactions, explicit approval for high-impact actions, and immutable audit records. [OWASP Cornucopia][8]

NIST’s current agent-identity work also centers on applying explicit identity and authorization controls to autonomous agents, while zero-trust guidance emphasizes just-enough, just-in-time authority that is removed when no longer needed. [NIST][9]

---

## 6. Container status: not yet Docker-like isolation

The present container implementation has valuable pieces:

* rootfs/pid-view model;
* resource-domain fields;
* container lifecycle;
* monitor reports and restart policy;
* OCI validation;
* image-layer/COW/volume bookkeeping;
* capability clearing on exit and fresh reacquisition on restart.

However, the repository explicitly records that:

* only one VFS lookup family is wired;
* global VFS functions can bypass the container view;
* there is no production task-to-container binding;
* PID lookup enforcement is absent;
* the container manager does not call a live spawn syscall;
* monitor reports are posted model events rather than real process-exit notifications;
* storage performs no actual VFS I/O or layer unpack;
* there is no QEMU lifecycle evidence.

OCI’s Linux configuration expects isolation surfaces covering mount, PID, network, IPC, UTS, user, cgroup and time namespaces, along with devices, resource control, security mechanisms and root filesystem setup. SimpleOS does not need to copy Linux internals, but it needs equivalent observable isolation semantics. [OCI runtime specification][6]

### Required isolation matrix

| Isolation plane | Current SimpleOS state | Required target |
| --- | --- | --- |
| Address space | Per-task address-space fields exist | Proven separate mappings and no unauthorized shared memory |
| Filesystem | Root-prefix model and partial VFS gate | Every path, FD, mount, rename and metadata operation uses caller domain |
| Process/PID | Explicit PID view model | Enforce lookup, signal, wait, debug and process-list visibility |
| IPC | Capability primitives exist | Private endpoint namespace and explicit routed cross-domain connections |
| Network | Basic flags/capabilities | Private stack or virtual interface plus egress policy |
| User identity | Not integrated with container | Rootless principal mapping and no host-equivalent root |
| Resources | `ResourceDomain` model | Live hierarchical CPU, memory, I/O, PID and network enforcement |
| Syscalls | Privilege mask model | Per-domain syscall filter that can only restrict |
| Devices | Typed device caps exist | Explicit device assignment, IOMMU and DMA confinement |
| Root filesystem | OCI adapter and layer model | Verified image ingest, bounded unpack, immutable layers and live COW |
| Lifecycle | ECS lifecycle model | Real spawn, exit event, reap, logs, attach, exec, stop, kill and restart |
| Storage recovery | Pure rollback/GC model | Transactional metadata and power-fail tests |
| Audit | Scattered model fields | Complete principal/delegation/action event stream |

A SimpleOS container should therefore be defined as a composition, not as a separate security mechanism:

```text
Container =
    Job
  + CSpace
  + IsolationDomain
  + ResourceDomain
  + ImageSnapshot
  + WorkloadIdentity
  + LifecycleMonitor
```

The same primitives also define services and agents:

```text
Service =
    WorkloadManifest
  + Job
  + CSpace
  + optional IsolationDomain
  + LifecycleMonitor

Agent =
    Service
  + ModelInfer capability
  + ToolInvoke capabilities
  + ApprovalPolicy
  + agent-specific budgets
```

---

## 7. Native container versus stronger untrusted-code sandbox

A correct native SimpleOS container can provide strong isolation, especially because SimpleOS is already moving toward per-process capabilities rather than Linux’s historically ambient authority. Nevertheless, native containers share the same kernel.

Use two security tiers:

### Tier 1: Native SimpleOS container

Appropriate for:

* first-party services;
* trusted local agents;
* normal applications;
* CI tasks with controlled inputs.

It uses separate address spaces, CSpaces, isolation domains, resource domains and syscall filters.

### Tier 2: Strong sandbox

Appropriate for:

* generated native code;
* arbitrary downloaded binaries;
* mutually untrusted tenants;
* agents executing code from untrusted repositories;
* browser-like hostile workloads.

Possible later implementations:

* a userspace application kernel, similar in concept to gVisor;
* a minimal hardware-virtualized SimpleOS guest;
* a microVM-backed container.

gVisor inserts a userspace application kernel while remaining OCI-compatible. Firecracker and Kata place workloads in lightweight VMs with a dedicated kernel and hardware-enforced isolation, while still relying on process-level constraints and resource controls for defense in depth. [gVisor][10]

In either tier, secret, policy, model and approval brokers must remain outside the untrusted sandbox.

---

## 8. Implementation architecture

### 8.1 Freeze these shared interfaces first

Create and freeze the following modules before parallel work begins:

```text
src/os/kernel/security/execution_context.spl
src/os/kernel/security/principal.spl
src/os/kernel/security/cspace.spl
src/os/kernel/security/job.spl

src/os/kernel/isolation/isolation_domain.spl
src/os/kernel/resource/resource_domain.spl

src/os/services/workload/workload_manifest.spl
src/os/security/policy/policy_compiler.spl
```

Suggested contracts:

```text
struct KernelCallContext:
    task_id: TaskId
    principal_id: PrincipalId
    job_id: JobId
    cspace_id: CspaceId
    isolation_domain_id: IsolationDomainId
    resource_domain_id: ResourceDomainId
    audit_context_id: AuditContextId
```

```text
struct WorkloadManifest:
    identity: WorkloadIdentitySpec
    image: ImageSpec
    authority: AuthorityRequest
    isolation: IsolationSpec
    resources: ResourceBudget
    lifecycle: LifecyclePolicy
    observability: ObservabilityPolicy
```

```text
struct CompiledExecutionPolicy:
    spawn_spec: SpawnSpec
    syscall_filter: SyscallFilter
    isolation_spec: IsolationSpec
    resource_spec: ResourceBudget
    identity_lease: IdentityLease
    audit_policy: AuditPolicy
```

Then specialize without duplicating the security model:

```text
ServiceManifest:
    workload: WorkloadManifest
    dependencies: [ServiceDependency]
    provides: [EndpointDeclaration]
    readiness: ReadinessPolicy

AgentManifest:
    workload: WorkloadManifest
    model: ModelPolicy
    tools: [ToolRoute]
    approvals: ApprovalPolicy

ContainerManifest:
    workload: WorkloadManifest
    image_snapshot: ImageSnapshotSpec
    volumes: [VolumeSpec]
    oci_compat: OciCompatibilitySpec
```

---

## 9. Phased implementation plan

### Phase 0 — Remove architectural ambiguity

#### Work

* Introduce `KernelCallContext`.
* Introduce `Principal`, `Job`, `IsolationDomain` and `ResourceDomain` IDs.
* Add those IDs to `TaskControlBlock`.
* Make syscall dispatch construct one immutable caller context.
* Change downstream kernel APIs to accept `KernelCallContext`, not scalar caller IDs.
* Merge `ServiceDef` and `ServiceManifest` around `WorkloadManifest`.
* Mark pure model APIs clearly as `model` or move them under model modules.
* Define one canonical capability implementation; remove or isolate disconnected capability stores.
* Add lint rules:
  * no new `CapabilitySet.full()`;
  * no caller-less security-sensitive syscall helper;
  * no global VFS access from userspace-request paths;
  * no raw text role check in kernel code.

#### Acceptance

* The filesystem exec gate receives the real calling TCB capability set.
* All spawn/exec/fork paths expose the same authority-computation trace.
* Existing unit tests remain green.
* A repository-wide authority-path report finds no unidentified caller.

### Phase 1 — Make process authority live

#### Work

* Wire `spawn_with_cspace` into every live process-creation path.
* Seed PID1 with concrete root capabilities and `RootMintAuthority`.
* Pass the child CSpace directly into TCB creation.
* Implement capability-handle lookup by type, rights and generation.
* Complete capability transfer through IPC.
* Implement recursive revocation by lineage.
* Make `exec` preserve or reduce authority; it must never silently gain rights.
* Make `fork` produce an attenuated child CSpace.
* Close all process-owned handles on exit.
* Turn the ambient-spawn seal on immediately after PID1 starts.
* Remove ordinary reachability of `spawn_full()`.

#### Acceptance

* Two instances of the same binary receive different CSpaces.
* Agent A cannot read, signal, connect to or inspect Agent B.
* A child requesting wider authority is rejected.
* A revoked parent token invalidates all descendants.
* Existing handles fail after generation revocation.
* No non-PID1 process can obtain root mint authority.

### Phase 2 — Build the real PID1 service manager

#### Work

* Boot only enough kernel machinery to mount/locate the init image.
* Start `/system/service_manager.smf` as PID1.
* Move architecture-specific service probes behind managed services.
* Load signed service manifests from VFS.
* Verify image hash/signature before granting authority.
* Build and validate the dependency graph.
* Reserve IPC endpoints before service startup.
* Implement endpoint activation first; add timer/device/path activation later.
* Implement start and stop ordering, readiness, health checks, watchdog, bounded restart, exponential backoff and jitter, restart-rate limiting, quarantine, clean shutdown, and log and exit-status capture.
* On service death, revoke the old CSpace; release device/secret grants; destroy or reset the job; reacquire all grants from policy; and spawn a fresh instance.

A production service manager normally combines dependency control, process supervision, watchdog/restart behavior and resource management. systemd is one reference implementation, including readiness modes, watchdogs, restart policies and restart rate limiting. [systemd][11]

#### Migration

* Adapt `driver_supervisor` to the generic supervisor API.
* Keep the device grant broker as a specialized broker.
* Convert VFS, network, display, storage and model broker to manifests.
* Replace inline boot HTTP service with a managed service.

#### Acceptance

Under QEMU:

1. PID1 starts VFS.
2. Network waits for VFS readiness.
3. HTTP waits for network readiness.
4. Kill network service.
5. Its device and endpoint grants disappear.
6. Supervisor restarts it with newly minted grants.
7. HTTP reconnects.
8. Restart storm eventually quarantines the service.
9. Shutdown stops services in reverse dependency order.

### Phase 3 — Enforce complete isolation domains

#### Filesystem lane

* Attach an `IsolationDomainId` to every task.
* Require caller context in all VFS operations.
* Eliminate or privatize global `g_vfs_*` entry points.
* Resolve manifest paths into directory handles.
* Enforce mount, rename, link, symlink and traversal rules.
* Apply checks both when opening and when using an FD.
* Add per-domain mount tables and read-only root support.

#### Process and IPC lane

* Enforce process-domain visibility for enumerate, wait, signal and debug.
* Give each domain a private endpoint namespace.
* Route intentional cross-domain connections through service manager capabilities.
* Ensure existing IPC handles remain explicit exceptions rather than namespace leaks.
* Add peer-death and cancellation events.

#### Network lane

* Give each isolation domain one of no network, broker-only network, a private virtual stack/interface, or explicitly shared network.
* Enforce egress by route/endpoint capability.
* Put DNS resolution behind a policy-aware broker.
* Account bytes and connections per resource domain.

#### Syscall lane

* Compile workload policy into a per-job syscall allowlist.
* Inherit it across child creation.
* Allow only additional restriction.
* Keep object-capability checks authoritative even for allowed syscalls.

#### Resource lane

Enforce hierarchical limits in scheduler, page allocator/VMM, process creation, block I/O, network, and handle allocation.

#### Acceptance

* Cross-domain path traversal, PID lookup, signal, IPC and network tests all fail closed.
* A fork bomb stops at the PID limit.
* Memory exhaustion is confined to the job.
* I/O and network throttling are observable.
* Killing a parent job terminates all descendants.
* No global API bypasses isolation.

### Phase 4 — Turn the container model into a runtime

#### Image and storage

* Initially support a local OCI bundle or tar import; registry pull can follow.
* Verify manifest, config and layer digests.
* Add image signature/trust-policy validation.
* Perform bounded, traversal-safe unpack.
* Store immutable content-addressed layers.
* Implement real VFS-backed COW snapshots.
* Implement persistent and ephemeral volumes.
* Enforce snapshot and volume quotas.
* Use transactional metadata updates.
* Add power-failure recovery tests.

The current OCI adapter and storage modules are policy/bookkeeping layers rather than live I/O implementations.

#### Lifecycle

* Make `container_manager.sys_start` submit a real `SpawnSpec`.
* Create a monitor capsule per container job.
* Deliver real kernel exit events.
* Implement create, start, state, logs, exec, attach, signal, stop with timeout, kill, restart, remove, snapshot, rollback and garbage collection.
* Make rootless the default.
* Map OCI configuration to SimpleOS isolation and resource domains.

#### Acceptance

A QEMU system test must demonstrate:

```text
import image
→ create
→ start
→ network request
→ inspect resource usage
→ crash
→ revoke all grants
→ restart with fresh grants
→ stop
→ remove
→ GC unused layer
```

It must also demonstrate failed cross-container filesystem, PID, IPC, network and device access.

### Phase 5 — Unified human/LLM/agent policy

#### Work

* Implement principal and session registry.
* Compile human roles, service roles and agent profiles through one policy compiler.
* Extend typed capabilities for secrets, models, tools, datasets and UI.
* Implement model broker, secret-use broker, network/egress broker, tool brokers, approval broker and audit service.
* Bind agent profile to image hash, parent session, tenant, task ID, expiry, allowed child roles and resource budget.
* Give each child agent a separate job and CSpace.
* Ensure a prompt or tool response can never modify its authority.
* Label memory/RAG records by tenant, source trust and data classification.
* Re-check authorization at each tool invocation.
* Add emergency stop that revokes and terminates the full agent subtree.

#### Acceptance scenario

A developer launches a code agent:

* It can read/write only the workspace.
* It can call the test broker.
* It has no raw network.
* It cannot read provider, GitHub or deployment credentials.
* It may spawn a test subagent with read-only source access.
* A malicious README instructing it to upload secrets has no effect because it lacks the capability.
* `git push` requires an approval token bound to the exact repository, branch and commit hash.
* Production deployment requires a second, separately authorized broker.
* Revoking the human session kills the agent subtree and invalidates all delegated handles.

### Phase 6 — Strong untrusted-code tier

#### Work

* Define `isolation_tier` in `WorkloadManifest`: `process`, `native_container`, or `strong_sandbox`.
* Keep the API identical across tiers.
* Initially use QEMU/KVM or another available VMM for the strong tier.
* Later consider a purpose-built minimal VMM or userspace application kernel.
* Keep brokers and credentials outside the guest.
* Use a narrow channel/vsock-like protocol.
* Destroy writable state after ephemeral execution.

#### Acceptance

* Untrusted code has no host filesystem or network by default.
* A compromised guest cannot obtain broker credentials.
* Resource and wall-time termination are enforced externally.
* Snapshot reuse does not retain prior tenant secrets.
* Host-side fuzzing and escape tests are mandatory.

### Phase 7 — Formal verification and adversarial evidence

Prove or model these invariants in Lean:

```text
child_authority ⊆ parent_delegable_authority

restarted_workload.old_grants = ∅

revoked(token) ⇒ all_descendants_invalid(token)

resource_usage(child_subtree) ≤ parent_budget

role_compile(request).authority
    ⊆ system_ceiling ∩ parent_ceiling ∩ image_ceiling

approval_token can_commit at most once

different_isolation_domains
    ⇒ no visibility absent explicit shared handle
```

Add syscall and IPC fuzzing; capability-transfer fuzzing; VFS traversal/rename/symlink adversarial tests; malformed OCI image tests; power-loss storage tests; policy-compiler differential tests; prompt-injection and tool-confusion tests; restart-storm and resource-exhaustion tests; and QEMU and board system tests.

---

## 10. Parallel-agent development split

Freeze the Phase 0 contracts first. Then assign non-overlapping ownership.

| Lane | Ownership | Main deliverable |
| --- | --- | --- |
| A — Process/CSpace | Scheduler, syscall caller context, loader, spawn/exec | Live least-authority process creation |
| B — PID1/Services | Boot, init service, service manifest, supervisor | Real service manager |
| C — Namespace/VFS/IPC | Isolation domain, VFS gates, PID and IPC view | No cross-domain bypass |
| D — Resources/Network/Device | Resource domain, scheduler limits, egress and device brokers | Enforced hierarchical budgets |
| E — Container Runtime | Container manager, OCI import, image/storage, monitor | Live container lifecycle |
| F — Human/Agent Policy | Principal registry, profiles, policy compiler, brokers, approvals | Unified role-to-capability pipeline |
| G — Evidence/Formal | Modern sspec, QEMU, fault injection, Lean, fuzzing | Independent acceptance evidence |

Shared files should be minimized. In particular:

* Lane A alone changes `TaskControlBlock`.
* Lane B consumes the frozen task/security interfaces.
* Lane C alone owns isolation-domain semantics.
* Lane D alone owns resource-domain semantics.
* Lane F alone owns policy compilation.
* Lane G must not repair implementation code while writing the primary acceptance tests.

Merge dependency:

```text
Phase 0 contracts
    ↓
Lane A process enforcement
    ↓
Lane B service manager ─┬─ Lane C isolation
                       ├─ Lane D resources
                       └─ Lane F policy/brokers
                              ↓
                       Lane E container runtime
                              ↓
                       Lane G full evidence gate
```

---

## 11. Highest-priority changes

Do these before adding more service, container or LLM policy models:

1. **Thread one real `KernelCallContext` through every syscall, exec and spawn path.**
2. **Inject a concrete child CSpace into the live TCB and permanently seal ambient spawning.**
3. **Boot a real userspace PID1 service manager from the filesystem.**
4. **Bind every task to an isolation domain and eliminate global VFS/security bypasses.**
5. **Make service restart revoke all old grants and reacquire them through brokers.**
6. **Only then connect the existing container and LLM-profile models to the live process path.**

The repository has already designed many of the correct mechanisms. The principal risk now is adding more parallel abstractions while the existing ones remain disconnected. The next milestone should therefore be:

> **One booted QEMU system where PID1 starts two capability-confined services and two instances of the same agent binary with different roles, proves that they cannot cross-access each other, supervises a crash without stale authority, and runs one rootless container through a real create/start/exit/reap path.**

## References

[1]: https://docs.sel4.systems/Tutorials/capabilities.html?utm_source=chatgpt.com "Capabilities | seL4 docs"
[2]: https://fuchsia.dev/fuchsia-src/concepts/kernel/rights?utm_source=chatgpt.com "Rights | Fuchsia"
[3]: https://fuchsia.dev/fuchsia-src/concepts/kernel/concepts?utm_source=chatgpt.com "Zircon Kernel Concepts | Fuchsia"
[4]: https://spiffe.io/docs/latest/deploying/svids/?utm_source=chatgpt.com "Working with SVIDs | SPIFFE"
[5]: https://www.kernel.org/doc/html/v5.9/userspace-api/seccomp_filter.html "seccomp filter"
[6]: https://github.com/opencontainers/runtime-spec/blob/main/config-linux.md "OCI runtime specification"
[7]: https://fuchsia.dev/fuchsia-src/concepts/components/v2/capabilities/directory?utm_source=chatgpt.com "Directory capabilities | Fuchsia"
[8]: https://cornucopia.owasp.org/cards/AAIK?utm_source=chatgpt.com "OWASP Cornucopia — Agentic AI"
[9]: https://pages.nist.gov/zero-trust-architecture/VolumeB/architecture.html "NIST zero-trust architecture"
[10]: https://gvisor.dev/docs/?utm_source=chatgpt.com "What is gVisor? | gVisor"
[11]: https://wiki.freedesktop.org/www/Software/systemd/ "systemd"

---

## Repository evidence merge (2026-08-11)

Parallel read-only review confirmed the assessment against the current tree.

- `TaskControlBlock` already owns a capability set, parent, address space, and
  `TaskIsolationProfile`, but not principal/job/CSpace/domain/audit identities
  (`src/os/kernel/scheduler/scheduler_types.spl`,
  `src/os/kernel/types/task_types.spl`).
- `spawn_with_cspace` and `fork_cspace` are strong pure models, while live fork
  copies the parent capability set and the filesystem-exec bridge cannot obtain
  the real caller TCB capabilities (`src/os/kernel/ipc/cspace_spawn.spl`,
  `src/os/kernel/scheduler/scheduler_exec.spl`,
  `src/os/kernel/loader/fs_exec_spawn.spl`).
- The filesystem-exec scalar gate correctly fails closed for nonzero callers,
  but only because its ABI lacks the calling TCB. The Phase 0 implementation
  now supplies `KernelCallContext` and a context-taking gate; syscall dispatch
  must construct that context from its live scheduler before this becomes a
  complete live path.
- The ring-3 ABI directly reaches state handlers that bypass the IPC model
  capability check. That dispatcher is concurrently owned elsewhere and must
  be migrated to the context API before this lane claims live syscall coverage.
- `os_main()` still performs synchronous hardware/VFS bring-up and inline HTTP
  or serial-shell handling. `InitService`, `ServiceManifest`, the driver
  supervisor, container manager, and LLM profile adapter are predominantly
  model/spec surfaces with no production supervisor/spawn ownership.
- Existing container VFS lookup enforcement is one optional global-view family;
  PID, IPC, network, device, resource, and task-to-container enforcement are
  not yet live per-caller boundaries.

The process, syscall/ABI, VFS/architecture, and boot files with concurrent
unrelated edits were not changed by this lane. The next merge point is the
frozen context API, not a parallel rewrite of those files.

## Implementation evidence update — 2026-08-11

The first live enforcement slice is now present: PID1 receives a
non-transferable root-mint binding; catalogue launches create fresh pledged
child CSpaces through the ordinary filesystem-exec spawn path; an exited child
cannot retain old grants. The target build produces static x86_64 and RV64
PID1 ELFs, and RV64 routes PID1 `Yield`, `WaitPid`, and opaque
catalogue-launch syscalls through the common stateful dispatcher.

This is not service-runtime completion. The source tree now has broker-backed
VFS/net/HTTP payload entrypoints, but no target-built or signed catalogue image
has booted them together. The pure-Simple image bake fails closed when PID1 is
selected but any catalogue image is missing. Named IPC catalogue grants map to
exact live endpoint checks and VFS transport uses the bounded copied-payload
ABI with one-shot reply permits; endpoint-handle generations, network route
enforcement, and target/QEMU proof remain open. The current status is tracked in
`doc/08_tracking/bug/catalog_service_named_capability_syscall_mismatch_2026-08-11.md`.

### Critical ABI hardening follow-up — 2026-08-11

The device `MapBar` boundary was not safe enough for a service/driver runtime:
the former syscall-83 ABI accepted a user-provided physical address and size,
while its live CSpace check was hard-coded to `0:0.0/BAR0`. The implementation
now makes the ABI `(packed PCI BDF, BAR index, optional user-VA hint)`. The
dispatcher checks that exact `DeviceBarMap` capability; the kernel verifies the
PCI function and resolves a memory BAR and its size itself. I/O BARs, missing
functions, invalid BAR indices, low/non-MMIO ranges, and partial map failures
fail closed; a partial page-table install is rolled back without freeing
device-owned memory. The user API now requires a `DeviceGrant`-shaped value and
cannot submit raw physical ranges.

Focused source checks completed without changed-file errors and contract specs
cover the exact BDF/BAR and no-raw-physical invariants. The interpreter test
runner did not print a final summary in this worktree, so it is not counted as
test-pass evidence. A bootstrap-seed RV64 native build of `os_main` initially
found and then, after repair, passed the former unsupported function-body
`@cfg` parse point, but emitted no output kernel artifact or actionable verdict.
It therefore remains a target-build blocker, not QEMU evidence. A subsequent
bounded build diagnostic established that the native-build wrapper was correctly
preserving compiler failure: discovery stopped at the concurrently untracked
`src/os/sosix/fs/ipc_codec_v1.spl:79` (`out.push(...)`, where `out` is parsed
as a reserved grammar form). The inactive lane's codec was repaired mechanically
by renaming only that reserved identifier; its focused source check then completed
without a changed-file diagnostic. The next native-build attempt did not reach
compilation because every candidate self-hosted compiler segfaulted during the
wrapper's environment-write capability probe. Thus there is still no RV64
artifact or QEMU evidence, now due to compiler bootstrap health rather than the
codec parser failure.

### Mission-critical integration update — 2026-08-11

The RV64 boot path now removes the dead inline-HTTP fallback entirely: after
the minimal kernel bring-up and root-filesystem probe it either prepares and
enters the filesystem-backed PID1 using the trap-owned scheduler, or returns
to the serial recovery shell with no service authority. PID1's restart loop
now uses a bounded exponential retry delay and deterministic per-service
stagger before a fresh opaque-catalogue launch; it quarantines after the
configured retry limit. This is restart policy evidence only: the service
payload sources exist, but they have not yet been target-built, signed, baked,
or run as a service-runtime claim.

The FAT32 descriptor path now stores the opening isolation-domain ID and
re-checks that domain on descriptor read/write. This closes a stale-descriptor
transition within the FAT32 route, alongside the existing live file-capability
rechecks. It is **not** filesystem namespace isolation: FAT32 remains globally
mounted, generic POSIX descriptor fallbacks retain no domain metadata, and a
per-domain mount/root table with caller-aware routing is still required.

The root service catalogue still labels executable bytes with a derived hash
rather than verifying a kernel-anchored signed trust record. Consequently the
catalogue must not be considered image-authenticating until bake emits a
signed fixed-ID/path/digest record and the kernel verifies its anchor before
parsing or minting any service authority.

### Lifecycle cleanup follow-up — 2026-08-11

PID1 can now unwind a partial dependency start through an opaque
`RootServiceStop` syscall. The kernel accepts it only from the current holder
of the non-transferable root-mint object and only for its live direct child;
it is not a general process-signal interface. Before publishing the target as
a zombie, the stateful trap path releases DMA/task resources, revokes the
child capability pouch, destroys its IPC endpoints, and clears its FAT32
descriptor metadata. The manager uses this operation in reverse dependency
order whenever endpoint readiness fails during VFS → network → HTTP startup.
Legacy result-only dispatch explicitly rejects this syscall because it cannot
preserve returned scheduler/IPC state. RV64 and x86_64 use the stateful route.

### PID1 lifetime follow-up — 2026-08-11

Exit of the root-mint PID1 is now a job-lifetime event: the stateful exit path
snapshots every live member of PID1's managed job subtree, releases each
member's DMA/task resources, revokes CSpace authority, destroys IPC endpoints,
and clears FAT32 descriptor metadata before atomically terminating the job
subtree. This prevents the former reparent-to-task-0 behavior from leaving
services alive after their sole supervisor dies. Ordinary process exit retains
normal reaper/adoption behavior; the recursive path is specific to the
non-transferable root-mint boundary.

### Managed driver ABI follow-up — 2026-08-11

The managed VirtIO-net and NVMe driver initialization paths now use the
capability-addressed MapBar ABI `(granted BDF, BAR index, VA hint)` rather than
passing `grant.bar0_phys`/`bar0_size`. NVMe now records the granted BDF and
passes it to AllocDma; if that managed allocation fails or returns a zero
address it fails closed rather than falling back to ambient `rt_dma_alloc`.
Bare-metal NVMe initialization retains its explicit non-managed mode. This
repairs the direct driver precondition for a future device broker, but the
broker, IOMMU enforcement, and target-native VFS/net payloads still do not
exist as a complete runtime.

### Root device broker follow-up — 2026-08-11

Live catalogue launch now asks a kernel-owned device broker to select the
first trusted NVMe controller for VFS or VirtIO network controller for net by
PCI class/subclass and vendor policy, rather than relying on a baked BDF. The
broker enriches only that child CSpace with exact `DeviceGrant`, BAR0 map,
bounded DMA, and IOMMU-domain capabilities; its syscall filter gains only the
corresponding grant/map/DMA/notification operations. `DeviceGrant` has also
become one-shot per task/BDF and is revoked on ordinary exit, PID1 subtree
exit, and catalogue stop. This is a concrete brokered device-authority path,
but actual IOMMU/DMA hardware confinement and signed catalogue images remain
separate completion requirements.

The brokered child can now consume its exact hardware assignment without a
baked BDF: `request_assigned_device_grant()` resolves the single concrete
`DeviceGrant` token in the child CSpace. Ambiguous, missing, or ambient device
authority fails closed. This is the required handoff primitive for real VFS
and net payload entrypoints; it is intentionally not a device-enumeration API.

### Network payload follow-up — 2026-08-11

`src/os/services/netstack/net_service_main.spl` is now a freestanding target
entrypoint for the catalogue's net slot. It consumes the sole assigned grant,
initializes `VirtioNetDriver` through its capability-addressed MapBar/DMA
paths, and starts `NetstackService`, which owns the exact `net` named endpoint.
It neither enumerates PCI devices nor accepts an input BDF or physical BAR.
The focused source/contract check passed. This is an individual payload
boundary, not boot/runtime evidence: VFS and HTTP peer payloads remain
unavailable, catalogue image signatures are not yet anchored, and the shared
RV64 build is blocked by the independently-owned `out` parser error.

### Native service transport follow-up — 2026-08-11

Owned-copy IPC now distinguishes a request from a reply. A request requires a
concrete `IpcConnect` right and mints exactly one reply permit only when it is
received. A reply requires and consumes that permit, and receiving it never
mints another. `ipc_reply_owned_v1` is used by the VFS and net service response
helpers, preventing reply-permit exhaustion during sustained request/reply
traffic. This fixes the transport prerequisite for a future HTTP payload, but
it does not itself add the native HTTP socket state machine or broker-side
`NetListen` enforcement.

The broker boundary now also checks the exact little-endian port in a native
`NET_BIND` IPC record before it enters the netstack. The caller must hold
`NetListen(port)` for that decoded port; malformed or too-short bind records
fail before queueing. `NET_LISTEN` itself cannot introduce an unbound external
port—the netstack only transitions an existing bound socket—so binding is the
authority-bearing operation. Per-client socket ownership remains a separate
netstack hardening task.

The VFS payload now carries a concrete `BrokeredFat32Filesystem` implementation
inside its target closure, backed by task-local NVMe and `NvmeBlockAdapter`.
That resolves the former source-level no-implementation duck-dispatch cause.
It still needs a native entry-closure/mount proof after the unrelated full-tree
parser blocker is resolved; no global boot VFS or endpoint-only replacement is
used.

The netstack now binds each socket descriptor to the authenticated source IPC
endpoint that created it. Bind, listen, connect, accept, send, receive, and
close reject a descriptor owned by a different endpoint; accepted descriptors
inherit their listener's endpoint. This closes the global-fd cross-client path
that remained after port capability enforcement.

`src/os/services/web/http_service_main.spl` now provides the catalogue HTTP
payload without `std.http_server` or hosted sockets. It creates the exact
`http` endpoint, connects only to `net`, performs native socket/bind/listen/
accept/read/send/close requests through owned records, and emits a bounded
HTTP/1.1 response. Its bind is covered by the kernel's exact `NetListen(80)`
gate and netstack socket endpoint ownership. This is focused source evidence,
not target/QEMU lifecycle evidence; a VFS target payload, image authentication,
and the blocked native build remain required for that claim.

`src/os/services/vfs/vfs_service_main.spl` now provides the matching VFS
payload. It consumes the assigned NVMe grant, creates a bounded
`NvmeBlockAdapter`, mounts it through a task-local `SharedFat32Driver`, and
starts `VfsService` on `vfs`. `BrokeredFat32Filesystem` is a concrete
`Filesystem` implementation in the target closure, avoiding both the kernel
boot singleton and the prior no-implementation duck-dispatch condition. Its
focused source check succeeds. A freestanding native artifact and mount proof
remain pending on a healthy target-native build; they are not implied by the
host source check.

### Native build gate update — 2026-08-11

The SOSIX IPC codec no longer blocks source discovery: every reserved `out`
identifier was renamed to `buffer` without changing the ABI or encoded bytes,
and the codec plus its unit specification completed the focused source check.
The immediate native-build gate is instead environmental: all candidate
self-hosted binaries (`bootstrap/stage2`, `bootstrap/stage3`, `release`, and
`bin/release`) segfault while `simpleos-native-build.shs` probes their
environment-write capability; the Rust seed is intentionally rejected by that
wrapper. Repair or redeploy a working self-hosted compiler before repeating the
native build. Do not interpret this as payload target validation.

### Agent runtime launch follow-up — 2026-08-11

`src/os/security/llm_profiles/agent_runtime.spl` now binds a
`CompiledAgentPolicy` to `launch_compiled_workload_into_scheduler`, the same
image-binding and child-CSpace mint seam used by the container runtime. The
agent-only runtime boundary rechecks nonzero child/model/tool budgets and a
nonempty approval contract before delegating; it does not mint a parallel
authority pouch. Model, tool, secret, UI, and approval operations remain
broker capabilities and the policy compiler continues to reject profiles that
request those unavailable brokers. The focused source check completed. The
interpreter test command exited successfully in this noisy worktree but did
not yield a compact final test summary, so it is not counted as independent
runtime evidence.

### Filesystem-view enforcement follow-up — 2026-08-11

Managed workload launch now binds one immutable, concrete filesystem root (or
the `none` deny-all view) to the child TCB after its process-view domain is
bound. `WorkloadManifest` rejects descriptive filesystem labels; it accepts
only an absolute root or `none`. The caller context carries that immutable
view, and every live FAT32 path syscall translates its normalized task-visible
path through the root *before* checking file capabilities and touching FAT32.
Thus a task rooted at `/workspace` sees `/src/main.spl` only as the concrete
object `/workspace/src/main.spl`; unbound and deny-all views fail closed.
PID1 and opaque catalogue services bind `/` explicitly, while agent/container
workload manifests now provide concrete roots. Existing FAT32 descriptor
domain checks remain in place for already-open handles.

This is a real root-view gate for the live FAT32 syscall family, not a complete
mount namespace: generic POSIX descriptor routes, symlink semantics, and
per-domain mount tables still need their own converged enforcement. Focused
source checking completed; the focused interpreter SSpec exited zero but the
runner emitted no final summary, so it is retained as limited evidence only.

### Container root binding follow-up — 2026-08-11

`ContainerRuntime.start_into_scheduler` now compares the compiled policy's
concrete filesystem root with the exact root in `ContainerWorld`'s kernel
namespace view before it calls the shared launcher. A missing view or any
mismatch—including a host-root `/` policy for a `/container/worker`
container—fails before a child TCB is created. This closes the control-plane
escape where a correctly image-bound container could request a wider workload
filesystem root than its container view. The container runtime source check
passed and its focused interpreter invocation exited zero, although the
repository runner again produced no compact final test summary.

### Agent delegation-depth enforcement follow-up — 2026-08-11

`compile_agent_policy` now rewrites every requested `ProcessSpawn` grant with
an attenuation depth capped by `AgentPolicySpec.allowed_child_depth` (or a
stricter pre-existing attenuation). This moves the value from advisory agent
metadata into the live capability lineage: every subagent spawn consumes the
same bounded ProcessSpawn token depth enforced by CSpace minting. Unsupported
agent broker dimensions remain fail-closed. The focused source check completed
and the policy SSpec invocation exited zero without a compact runner summary.

The agent runtime independently rejects a mutable compiled policy if any
`ProcessSpawn` grant has unlimited or wider-than-declared depth before it calls
the generic launcher. This does not replace the compiler or kernel mint check;
it prevents the runtime adapter itself from becoming a widening seam. Its
focused source check passed and the amended runtime spec invocation exited
zero without a compact summary.

### Legacy descriptor bypass closure — 2026-08-11

Managed tasks now fail closed when attempting to read or write an old
`FD_TYPE_FILE` numeric VFS descriptor. That legacy backend does not retain
the opening isolation domain or concrete object capability and therefore
cannot satisfy the new caller-aware filesystem contract. FAT32 descriptors
continue through their domain/path checks; pipes, sockets, serial, and legacy
unbound compatibility tasks are unaffected. A production replacement must
carry equivalent caller-bound metadata before this route is re-enabled. The
focused source check completed and the authority spec invocation exited zero
without a compact test summary.

### Live CSpace revocation follow-up — 2026-08-11

The stateful `CapRevokeTransitive` syscall path now revokes tokens from the
actual scheduler-owned TCB CSpaces, not only the older IPC capability-manager
ledger. It computes provenance closure across every live task, removes the
root token and all descendants atomically from their owners, and advances each
affected CSpace binding generation. The compatibility ledger is updated after
the authoritative scheduler mutation. The focused scheduler lineage spec
exited zero after a parser correction; as with other focused interpreter runs,
the runner did not emit a compact summary.

### Native service payload and trust-chain boundary — 2026-08-11

The PID1 catalogue may reserve and supervise VFS, network, and HTTP workloads,
but those names must not be treated as bootable native services yet. The
current VFS implementation reaches a `Filesystem` trait dispatch that the
freestanding target lowers to `DUCK_DISPATCH_UNSUPPORTED_SLOT`; the current
network path is a kernel-global hardware bootstrap unless a concrete device
grant is brokered; and the existing web server uses hosted sockets/threads,
not the SimpleOS IPC/network ABI. The owned IPC transport now marks replies,
mints reply permits only for received requests, and consumes them on matching
reply sends; this closes the permit-leak prerequisite for a future HTTP loop,
but it does not provide a complete socket ABI or make the hosted server
freestanding. A PID1 launch must quarantine or report these unavailable
payloads rather than silently falling back to global kernel services.

The planned root catalogue signature check also has a non-negotiable release
input: a real, release-owned public key and a host-only signing-key path. A
narrow repository search found no configured root-catalog trust anchor. The
loader must therefore remain unauthenticated-but-explicitly-not-production
until that key is supplied; no fixture, SSH key, or generated test key may be
promoted to a root of trust. The intended verifier is the authoritative
freestanding `os.crypto.ed25519.ed25519_verify` implementation, binding exact
service bytes, canonical path, identifier, and target architecture before any
RootMint delegation.

### Forced-exit resource teardown follow-up — 2026-08-11

The installed stateful syscall dispatcher now handles `Term`, `Kill`, and
`Interrupt` as one teardown transaction: release DMA allocations and tracked
lifecycle resources, revoke device grants and IPC capabilities, destroy the
target's endpoints, erase FAT32 task records, and only then publish the
scheduler zombie transition that clears its live CSpace. The result-only
compatibility dispatcher rejects these destructive signals, because it cannot
return the mutated IPC state without risking stale endpoint/device authority.
`Stop` and `Continue` remain non-destructive state transitions. This closes a
previous gap in which explicit service stop used full cleanup but ordinary
signal termination could retain non-TCB authority. The focused source check
completed with warnings only; the broad interpreter SSpec runner again did
not emit a compact final summary, so target-runtime evidence remains pending.

### Agent emergency-stop teardown follow-up — 2026-08-11

`terminate_agent_subtree` now requires and returns the live `IpcManager` along
with the scheduler. After it confirms controller-job ancestry, it walks every
member of the target agent job, runs the same forced-exit resource teardown
used by the stateful signal ABI, then terminates the job tree. An emergency
stop therefore invalidates task-owned IPC endpoints and capability ledger
entries in addition to clearing CSpaces, DMA/device grants, lifecycle records,
and FAT32 descriptor records. The focused source check completed without
changed-source diagnostics; the interpreter SSpec invocation emitted no
compact final verdict in this worktree, so it is not independent runtime proof.

### PID1 service-stop subtree follow-up — 2026-08-11

`RootServiceStop` now treats the catalogue service job—not merely its direct
leader process—as the lifetime boundary. PID1 authorization remains restricted
to a live direct catalogue child, then the scheduler terminates every member
of that child job while the stateful dispatcher tears down each member's
non-TCB authority before it publishes the new scheduler state. This prevents a
forked/worker service member from surviving supervisor stop or restart with a
live endpoint, device grant, DMA allocation, or CSpace. The root-catalogue
unit spec now creates a cloned job member and asserts both leader and worker
are zombies with empty CSpaces. Focused source checking completed with the
repository's existing warnings; target boot/QEMU evidence remains blocked.

### Container monitor-exit teardown follow-up — 2026-08-11

`ContainerRuntime.reconcile_exit_from_scheduler` now accepts and returns both
the scheduler and `IpcManager`. Once it observes a genuine zombie for the
container leader, it tears down that leader and every live job member, then
terminates the remaining job before posting the monitor observation that may
permit a restart. The container runtime can no longer treat a scheduler zombie
as a model-only event while worker endpoints, capability entries, device/DMA
records, or descriptor state remain live. The focused source check completed
without changed-source diagnostics; its interpreter test invocation produced
only repository bootstrap warnings and no compact final verdict.

### Unified task-exit teardown owner — 2026-08-11

The non-TCB exit cleanup is now centralized in
`os.kernel.lifecycle.task_exit_teardown`, keyed only by stable `TaskId` and
explicit `IpcManager` state. Normal exit, PID1 service stop, forced signal,
agent emergency stop, and container monitor reconciliation all call that same
idempotent transaction. It releases DMA/device leases, lifecycle records, IPC
capability and endpoint state, and FAT32 task metadata independently of when
the scheduler clears the CSpace. This replaces the former syscall-handler
coupling and makes post-zombie monitor cleanup safe. A direct unit spec covers
endpoint removal and repeated invocation; its interpreter invocation emitted
no compact runner verdict in the current bootstrap environment.

### Hierarchical process-budget enforcement follow-up — 2026-08-11

Managed process admission now counts the caller's complete live
resource-domain subtree instead of only direct children. A managed child gains
a fresh resource domain linked to its parent; fork/clone shares that domain.
The new scheduler traversal follows those links with a bounded cycle guard, so
grandchildren cannot evade an ancestor's `process_limit` by inserting another
process layer. Both manifest-backed process limits and `SpawnSpec.budget` use
this authoritative count before image creation. The focused source check
completed without changed-source diagnostics, and
`resource_domain_budget_spec.spl` passed in the interpreter (1 file, 1 result,
1 passed).

The adjacent `memory_pages` policy remains only partially live: PID1 and
managed-workload launch bind it into `TaskIsolationProfile.max_memory_pages`,
but the current VMM/mmap/brk allocation paths do not yet charge or reject by
that field. It must not be represented as a completed memory controller until
page accounting is attached to those paths and tested under exhaustion.

### Per-task mapped-memory enforcement follow-up — 2026-08-11

Anonymous `mmap` now reserves pages in a task-keyed budget ledger before PMM
allocation, rolls that reservation back on map or ownership-registration
failure, releases it after owner-validated `munmap`, and clears it during the
shared task-exit teardown. The effective task ceiling is the immutable
`TaskIsolationProfile.max_memory_pages` bound by managed workload policy.
Pre-ledger/kernel mappings may still unmap successfully without an invented
charge. This is live per-task mapped-page control, not yet aggregate memory
accounting across a full resource-domain subtree or demand-paged/file-backed
memory. `task_memory_budget_spec.spl` passed in the interpreter (1 file, 1
result, 1 passed).

### Hierarchical mapped-page admission follow-up — 2026-08-11

Anonymous `mmap` now also performs a live resource-domain ancestry admission
check before reserving its per-task charge. For every ancestor domain, it sums
the non-zombie tasks' mapped-page charges and rejects a request that would
exceed that domain's immutable `max_memory_pages` ceiling. This closes the
child-fan-out bypass where individually conforming children could collectively
exhaust a parent's memory allocation. The check has bounded lineage traversal,
fails closed on a malformed cycle, and saturates charge accumulation rather
than permitting integer wraparound.

The accounting remains limited to anonymous mappings created through the live
memory syscall. File-backed mappings, demand paging, and resource accounting
outside this syscall remain open work. The focused source check completed
without changed-source diagnostics. The current interpreter invocation of
`resource_domain_budget_spec.spl` produced bootstrap-warning output without a
compact test summary, so it is intentionally not recorded as a PASS result.

### DMA mapped-page budget follow-up — 2026-08-11

The live `AllocDma` path now reserves the caller's task charge only after the
same full resource-domain ancestry admission used by anonymous `mmap`.
Every post-reservation failure path returns the charge, `FreeDma` returns the
matching rounded page charge after releasing the allocation, and the shared
task-exit teardown remains the idempotent fallback for abandoned DMA buffers.
This prevents a device service from escaping its memory ceiling via
physically-contiguous allocation. The focused source check of the device
dispatcher and ABI shim completed without changed-source diagnostics; target
DMA/IOMMU execution evidence is still required.

### BAR mapping lifetime follow-up — 2026-08-11

`MapBar` now registers each successful MMIO virtual range as the task's
`RES_BAR_MAPPING` before returning it. If registration cannot be recorded, it
rolls back the page-table mappings and reports allocation failure. `munmap`
classifies a request against tracked BAR ranges: an exact range unmaps and
removes its cleanup record, while a partial or cross-range request is denied.
This prevents stale exit cleanup from unmapping a later unrelated mapping at
the same virtual address. Exact BAR unmap drops only PTEs, never returns a
borrowed MMIO physical address to the PMM. Generic `munmap` rejects any overlap
with a tracked DMA buffer; only `FreeDma` may validate and release its device
and IOMMU-bound allocation. `mprotect` likewise rejects both BAR and DMA ranges,
preserving their kernel-installed NX attribute. The source check completed
without changed-source diagnostics. The focused BAR lifecycle test ran, but the
current bootstrap runner truncated its compact result summary, so no PASS
verdict is claimed.

### VM compatibility mmap enforcement follow-up — 2026-08-11

The older `sys_mmap`/`sys_munmap` ABI is now charged through the same live
task and ancestor-domain page-admission path as the newer memory syscall.
Failed mapping rolls the reservation back; successful non-device unmap returns
it. Its unmap path now applies the BAR/DMA lifetime policy too. Exact BAR
unmaps use a new transactional borrowed-MMIO primitive that rolls PTE failures
back but never invokes `pmm_put_page`; DMA overlaps fail closed so `FreeDma`
retains device/IOMMU validation. The focused VMM/SPM/dispatcher source check
completed without changed-source diagnostics. The underlying VMM currently has
an independently documented VMA value-propagation limitation, so this is not
evidence of complete file-backed/shared mapping correctness or target runtime
execution.

### Device and VM syscall context follow-up — 2026-08-11

The device-grant, BAR, DMA, and compatibility VM mapping handlers now receive
an immutable `KernelCallContext` built once from the scheduler's current live
TCB at dispatch. Their resource ownership derives from `context.task_id`; a
missing current TCB fails closed before entering the sensitive handler. This
removes scalar caller-ID plumbing from these paths and keeps the live CSpace,
principal, job, isolation-domain, and resource-domain record available to
future policy checks at the same boundary. It does not yet migrate every
legacy syscall helper, so the repository-wide caller-context criterion remains
open.

### Live fair-share CPU binding follow-up — 2026-08-11

`ResourceBudget.cpu_weight` is now compiled only when it is nonzero and at
most the scheduler's fair-share maximum (4096). Managed workload launch binds
that value exactly once after memory/process limits. The scheduler installs it
into the child's live fair scheduling configuration and clamps a nested managed
child to an already-bound parent weight, so a downstream manifest cannot widen
its individual CPU-share authority. Fork carries the bound schedule/domain
state without creating a new wider policy binding. This is live per-task fair
share enforcement, not yet a group-wide CPU quota: sibling weights can still
sum beyond a parent's desired aggregate share. The focused source check
completed without changed-source diagnostics; the launch spec's compact test
summary was truncated by the current bootstrap runner and is not counted PASS.

### Native target toolchain recheck — 2026-08-11

The prior full-source parse blocker in `src/os/sosix/fs/ipc_codec_v1.spl` has
been removed by its owning lane. The native SimpleOS build now fails at an
earlier independent admission point: every available self-hosted compiler
segfaults during the build script's environment-write capability probe. The
script correctly rejects the Rust bootstrap seed, so no native PID1 or service
artifact can be claimed. The exact resume command is
`sh scripts/os/simpleos-native-build.shs` after deployment of a functioning
self-hosted compiler.
