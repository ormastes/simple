<!-- codex-architecture -->
# Simple Container across native hosts

Status: proposed platform architecture, updated 2026-09-27 for native execution on each OS. Privilege policy and platform activation remain pending; this document is not a live support claim.

Product direction clarified 2026-09-28: **Simple Container** is the portable
container API and lifecycle owner. Podman is an interim Linux OCI engine behind
that API, not the product or the cross-platform implementation. The current
`OCI_DEFAULT_ENGINE = podman` constant selects only the Linux adapter's engine.
The implementation policy is Simple `.spl` for provider orchestration and
platform logic. Platform C APIs may be declared at a Simple SFFI boundary when
an existing callable surface supports them; no new C implementation is part
of this work.
After an in-tree Simple Linux provider proves equivalent rootless isolation,
resource policy, native exit, cancellation, recovery, and exact-ID cleanup on
a live Linux host, make that provider the Linux default and retain Podman as an
explicit compatibility backend. Keep Windows HCS process containers, FreeBSD
jails, macOS native sandbox, and SimpleOS kernel containers as separate native
leaves under the same Simple Container contract. No host silently substitutes
Podman, a Linux guest, or a VM for its native leaf.

## Scope and existing seams

The requested hosts are Linux with rootless execution, Windows Server with process-isolated native Windows containers, FreeBSD with an OCI/jail provider, and macOS with native App Sandbox execution. SimpleOS uses its native kernel container provider. Each provider runs programs for its own OS. A VM is outside Simple Container admission.

`src/lib/common/contracts/container/runtime_v1.spl` owns `RuntimeIdentityV1`, `RuntimeOperationV1`, and the pure transition oracle. Platform providers own command construction, execution, observation, and mutable state. Its `RuntimeProviderV1` trait currently exposes only `probe`; this proposal does not pretend it has mutable lifecycle methods.

`src/lib/nogc_async_mut/container/providers/linux/oci_runtime_v1.spl` is the existing Linux adapter. Its rootless checks and actual runtime configuration require live verification. `src/os/services/container/runtime_provider_v1.spl` binds the shared envelope to `ContainerRuntime.start_into_scheduler` and authoritative scheduler exit observations. It explicitly advertises no logs or durable recovery. `container_manager.spl` remains userland policy state; `src/os/kernel/loader/container_namespace.spl` enforces the kernel boundary. OCI import is policy translation and does not make a foreign kernel ABI executable.

## Composition and ownership

Use common value contracts plus sibling provider adapters. This fits existing seams and keeps host APIs out of common contracts. A single universal subprocess driver would conceal incompatible privilege and lifecycle semantics. A mandatory VM would violate the requested native host routing. Neither is selected.

| Owner | Authority | Boundary values |
|---|---|---|
| Common contracts | Validate metadata and lifecycle transitions | Copied/frozen requirements, capabilities, identities and observations |
| Host provider | Native workload identity, journal, handles and lifecycle state | Bounded encoded operation results; opaque identity-bound handles |
| Optional broker | Scoped native host authority, if selected and provisioned | Authenticated caller request and generation-bound authorization |
| Build/test controller | Requested host/guest/isolation and evidence acceptance | Frozen request; validated result committed by controller |
| SimpleOS runtime/kernel | Container policy, scheduler task, namespace enforcement | Owned scheduler/IPC results returned to their caller |

Common nodes live in `src/lib/common/contracts/container/`. Host siblings consume those nodes and never import each other's private leaves. MDSOC encapsulates host adapters; the SimpleOS userland manager retains its existing ECS arrays. Kernel and driver enforcement remains MDSOC-only. No ECS redesign or ABI/layout rewrite is necessary.

One provider owner serializes operations for a workload identity. Child execution produces fresh observations; the owner validates operation, generation, boot identity and native identity before committing state. Cancellation closes admission and drains bounded results; late results cannot revive a cancelled attempt. No raw pointers or borrowed mutable host objects cross a process boundary. Existing scheduler/IPC value returns must be reassigned by their owner.

## Capability routing

`ContainerHostRequirementV1` and `ContainerHostCapabilityV1` in `host_capability_v1.spl` express exact host, guest, isolation and client-privilege constraints. `container_host_admission_reason_v1` succeeds only with an empty reason. Discovery alone cannot establish `launch_capable`. SDN receipts describe a provider observation; parsing an arbitrary receipt never grants native authorization.

| Host | Intended native route | Admission prerequisites | Evidence still required |
|---|---|---|---|
| Linux | Interim rootless Podman OCI adapter; later in-tree Simple Linux provider | Supported user namespace/id mapping, writable user storage, usable runtime and required resource/network facilities | Execute as ordinary user; prove isolation, exit and cleanup before changing the default |
| Windows Server | Windows container runtime over HCS | Compatible Windows image/host build and configured service authority; process isolation when native-container is requested | Native Windows lifecycle plus ordinary-client authorization boundary |
| FreeBSD | FreeBSD OCI runtime backed by jails | Matching FreeBSD image/ABI, configured jail/storage/network facilities and selected authority | Native jail identity, policy enforcement, exit and cleanup |
| SimpleOS | Managed task/container adapter | Valid execution policy and kernel-provided scheduler/context | Existing managed launch/exit evidence; optional features remain unavailable |
| macOS | Signed App Sandbox helper and owned native process | macOS program, verified entitlements, signed helper, selected native-sandbox policy | Actual sandbox denial, native exit, cleanup and same-owner limitation |

Hyper-V isolation is a virtual-machine capability and is rejected by Simple Container. Linux image metadata on Windows or FreeBSD does not imply native Linux execution. Runtime presence, version output and package installation are preflight observations only.

## Privilege alternatives pending selection

**Strict unprivileged execution:** every admitted launch uses a user provider. It best matches rootless Linux but can leave Windows/FreeBSD launch unavailable. No automatic elevation is allowed. If the user selects zero administration even during setup, the controller also rejects `admin_setup: true`, including rootless providers needing administrator provisioning.

**Unprivileged client with one-time privileged provisioning:** Linux remains rootless; other hosts may use a narrowly scoped broker. A successful ordinary CLI invocation then describes delegated authority, not a rootless backend. Provisioning, service ownership, ACLs, allowed images/mounts/network operations and revocation require a separately approved design.

`client_privilege` distinguishes `user`, `delegated`, and `unavailable`; `admin_setup` reports whether setup needs administration. `require_unprivileged_client` alone cannot distinguish strict rootless from an authorized delegated client. Therefore the controller must retain the user's selected execution policy outside this v1 request and reject delegated routes under strict policy. No choice is inferred from a boolean or from a receipt.

The research lane reports that FreeBSD's documented Podman jail route currently requires root. That route cannot become a `user` provider merely by putting an ordinary CLI in front of it; any delegated route remains a separate proposed mechanism. Apple's Linux container VM facilities are outside Simple Container. A signed App Sandbox helper is the proposed Mac route; it is a `native-sandbox` capability rather than a native kernel container. Consult the companion domain research for platform sources and version qualifications.

## Startup, latency and evidence

Probe once per explicit preflight or provider-session initialization. Cache static runtime metadata by executable identity/configuration and invalidate on replacement or configuration change. Never cache authorization across broker reconnect, user change, reboot or generation change. Revalidate workload identity before every mutation; retain live handles rather than scanning all containers per request.

Record warm probe duration, create/start/wait/destroy duration, timeout/cancellation outcome and peak RSS with host/runtime versions. Numeric budgets remain requirement options until selected. Tests must not report performance compliance without a selected threshold and measured fixture. Build-host handoff SDN and container capability SDN have distinct schemas and evidence meanings.

See [detail design](../05_design/simple_container_cross_host.md), [test plan](../03_plan/sys_test/simple_container_cross_host.md), and [lane ownership](../03_plan/agent_tasks/simple_container_cross_host_parallel_2026-09-26.md). Root merges and Astra reviews executable evidence; additional sidecars are N/A for this design lane.
