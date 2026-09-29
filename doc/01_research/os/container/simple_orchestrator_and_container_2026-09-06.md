# Simple Orchestrator and Simple Container
## SDN/Simple authoring, Kubernetes vocabulary, MDSOC++ architecture, native-host ports, and real-network CI

**Date:** 2026-09-06  
**Repository:** `ormastes/simple`  
**Inspected revision:** `0dc18e8edfc86ea19c81fc6d38fb606d4d0483b1`  
**Status:** research-backed proposed design and implementation plan; no implementation or cross-host execution is claimed.  
**Initial execution cohort:** Linux, Windows, macOS.  
**Subsequent execution cohort:** FreeBSD, SimpleOS.  
**Primary language:** Simple. Configuration is SDN; optional authoring/build logic is ordinary Simple script.  
**Architecture:** userland MDSOC++ over the shared composition/kernel-plugin foundation; OS enforcement remains in the host kernel and its existing runtime interfaces.

## Executive decision

Build **one Simple Orchestrator**, **one portable Simple Container management library**, and **small host-specific runtime/network/storage providers**. Use Kubernetes resource names and ownership semantics, but a deliberately scoped Simple-native API rather than an unsupported claim of full Kubernetes compatibility.

The chosen combination is:

```text
SDN resources                 ordinary Simple manifest-building script
      |                                      |
      +---------- strict typed validation ---+
                             |
                  immutable canonical ResourceSet
                  + artifact/plugin/input locks
                             |
                 plan / authorize / apply API
                             |
              MDSOC++ orchestration control plane
              controllers -> placement -> committed bindings
                             |
                   one node agent per host
                             |
                 shared Simple Container core
                             |
      +-------------+-------------+-------------+-------------+
      |             |             |             |             |
 Linux OCI    Windows HCS    macOS native    FreeBSD jail   SimpleOS
 crun/runc    process mode   sandbox/process  /ocijail       containers
      |             |             |             |             |
 host kernel   host kernel    Darwin kernel   host kernel   Simple kernel
```

**Important qualification:** macOS native application sandboxing is not equivalent to Linux/Windows/FreeBSD kernel containers. Apple's Linux-container product uses VMs. Therefore macOS participates natively through an explicitly weaker/different `native-sandbox` or trusted `native-process` workload class; a `native-container` requirement must not silently fall back to either. An optional Apple Linux-VM provider is separately named and requires explicit permission. [E01, E02, E03, E04]

Windows **does** support real process-isolated Windows containers sharing its kernel. This is not a new 2026 capability. The native Windows backend must select process isolation and an allowed host/image compatibility combination; WSL2 or Hyper-V-isolated execution does not satisfy the native-container lane. [E01, E05]

A shared orchestration API is feasible. A universal image, identical kernel features, and identical isolation guarantees across all five systems are not assumptions this design makes.

---

## 1. Scope, terminology, and requirements

### 1.1 Scope boundaries

This project provides local container management, a node agent, a declarative cluster API, controllers, placement, service endpoint management, build/test scheduling, and evidence-producing CI. It does not initially implement a Linux ABI for SimpleOS, a Darwin equivalent of Linux namespaces, a new distributed filesystem, or a complete Kubernetes distribution.

Here **SDN means Simple Data Notation**, not software-defined networking. **Kernel-plugin** means the application composition kernel: it does not mean installing new Windows drivers, Linux kernel modules, or macOS kernel extensions. **Native** means the workload uses the target host OS kernel without introducing a separate guest kernel for that workload. A Windows test host may itself be a VM while its process-isolated containers still use that Windows host kernel; host virtualization and workload isolation must be recorded separately.

### 1.2 Acceptance requirements

| ID | Requirement | Acceptance boundary |
|---|---|---|
| ORCH-001 | Author resources in existing SDN syntax | Strict parse, schema validation, source locations, negative fixtures |
| ORCH-002 | Author reusable configurations in ordinary Simple | Script emits the same canonical resource model; no scheduler-side script execution |
| ORCH-003 | Use Kubernetes vocabulary | Defined Pod/Deployment/Job/Service/Node semantics and conversion tests |
| ORCH-004 | Reuse MDSOC++ and composition | No duplicate loader, registry, async operation lifecycle, or ABI |
| ORCH-005 | One portable container-management core | Non-provider code contains no host syscalls or `os.kernel.*` imports |
| ORCH-006 | Native Linux containers | Real OCI launch, kernel isolation/resource evidence, cleanup |
| ORCH-007 | Native Windows containers | Process isolation, compatible Windows image, HCS/runtime evidence |
| ORCH-008 | Honest native macOS execution | Actual Darwin workload; sandbox capabilities verified; no container-equivalence claim |
| ORCH-009 | Later native FreeBSD containers | Jail/ocijail identity, VNET, resource and cleanup evidence |
| ORCH-010 | Later SimpleOS containers | Existing live-launch bridge, real task/namespace/network evidence |
| ORCH-011 | Minimize host variance | Common lifecycle, resources, ownership, errors, artifact identity, logs, and CI contracts |
| ORCH-012 | Real cross-host network CI | All six directed Linux/Windows/macOS paths execute inside real workloads |
| ORCH-013 | Distributed failure correctness | Recovery, stale-state rejection, partition tests, and fencing where required |
| ORCH-014 | Truthful support reporting | PASS/FAIL/BLOCKED/UNSUPPORTED/NOT_RUN are distinct; discovery is not execution |
| ORCH-015 | Bounded no-GC async hot paths | Explicit queues, backpressure, generations, cancellation and retirement |
| ORCH-016 | Secure supply chain and authority | Digest locks, explicit capabilities, authenticated nodes, least-privilege CI |

### 1.3 Non-goals for the first release

Do not implement full Kubernetes API-server compatibility, transparent cross-OS live migration, arbitrary Linux images on non-Linux kernels, automatic weaker-isolation fallback, new consensus algorithms, global region federation, or GPU/FPGA scheduling beyond typed capability declarations. Do not equate a compile-only port with an operational host port.

---

## 2. Verified Simple baseline and consequences

All code observations below are pinned to the revision on the cover. Source inspection establishes implementation structure, not successful execution or security certification.

| Area | What was verified | Consequence |
|---|---|---|
| SDN | `src/lib/common/sdn/parser.spl` exposes scalar/collection parsing, spans, and issues. Ordinary parsing resolves duplicate keys last-wins. [R01] | Add a strict orchestration profile over the canonical parser; reject duplicate keys. Do not fork the parser. |
| Container manager | `container_manager.spl` is a userland MDSOC+ capsule with an ECS-style `ContainerWorld`, Pod membership, resource/lifecycle components, and model spawn requests. [R02] | Preserve its useful local ownership model, but do not call the manager itself the isolation boundary. |
| Live execution | `container_runtime.spl` checks image/policy hash and filesystem root, launches a real scheduler task through the managed-workload seam, binds PID, and reconciles real zombie exits. [R03] | Keep this as the SimpleOS runtime adapter; do not import it into every hosted build. |
| OCI import | `oci_import.spl` explicitly accepts pre-parsed normalized input and performs no pull, unpack, or filesystem I/O. Its path rules are a textual model. [R04] | Real registry transport, verified extraction, platform matching, and host path enforcement are separate deliverables. |
| Container source inventory | The service directory includes manager, runtime, storage, and OCI import files. [R05] | Inventory and test storage behavior before extracting it; file presence is not a durability guarantee. |
| Composition ABI | `provider_contract.spl` uses fixed-width records/arena offsets, interface versions, capability requests and opaque local handles. [R06] | Reuse this boundary. Do not export Simple collections or objects across a stable ABI. |
| MDSOC++ predecessor | The September 3 plan explicitly proposes the reusable async kernel-plugin layer and reuses synchronous composition. [R07] | Treat it as architectural authority, not proof of implementation. |
| Async kernel-plugin readiness | The verification addendum records the async directory as absent; a direct read of that directory also returned not-found at this snapshot. [R08] | Make the shared implementation a dependency. A static slice can proceed without inventing another framework. |
| SOSIX | The unification design selects shared operation/ring contracts and a hosted facade, and leaves non-Linux provider work explicit. [R09] | Reuse its lifecycle, error and authority model; do not assume all host bindings already exist. |
| CI | The inspected Docker/Podman unit/integration jobs invoke `test ... --list`. [R10] | They provide discovery evidence, not actual test execution or heterogeneous-network proof. |

### 2.1 Corrections to the previous assessment

The repository is not merely documentation: it has concrete container state and a live SimpleOS launch bridge. However, the earlier description of a nearly complete portable container foundation was too broad. Image I/O, real host adapters, isolation conformance, durable recovery, and cross-host execution need their own evidence.

Likewise, adding a demonstration node registration service is modest work; producing a secure, recoverable, heterogeneous orchestrator is a substantial project. Its difficult parts are failure semantics, platform-specific enforcement, networking, storage ownership, artifact compatibility, and reliable qualification—not just sending a remote launch request.

### 2.2 Readiness gate before coding

Record a baseline manifest containing the exact compiler/runtime artifact, source revision, executable digest, host OS/build, ABI, available shared libraries, provider digests, and actually runnable tests. Resolve whether each host can run a supported interpreter, a native compiled executable, or only a bootstrap shim. A shim that cannot execute the relevant command is `BLOCKED`, not a valid performance baseline.

---

## 3. Comparative research and the selected architecture

### 3.1 What to adopt from other systems

These are design comparisons, not unsupported market-share scores.

| System | Relevant structure | Adopt for Simple | Do not copy blindly |
|---|---|---|---|
| Kubernetes | Declarative resources, Pods, controllers, ownership and status; Windows has a distinct feature profile. [E06, E07] | Vocabulary, reconciliation, readiness, versioned object identity, visible unsupported fields | Full ecosystem and API semantics before they can be implemented/tested |
| Nomad | Server/client split, resource fingerprinting, placement, allocations, task drivers. [E08, E09] | Compact host agent, recoverable drivers, placement separate from execution | Nomad's generic `job` terminology in the Kubernetes-facing resource model |
| Nomad HCL | Client-side HCL parsing produces JSON API input; job/group/task hierarchy. [E10] | Separate authoring language from canonical API data | A second native HCL parser or runtime when SDN/Simple already exist |
| Terraform | Write/plan/apply infrastructure workflow. [E11] | Reviewable plans, immutable inputs, explicit changes | Treating one-time provisioning as continuous workload reconciliation |
| CUE | Values and constraints participate in validation. [E12] | Closed schemas, composition checks, early rejection | Another mandatory evaluator in the node agent |
| Pkl | Typed, modular configuration authoring. [E13] | Reusable typed configuration libraries | Another source language alongside Simple |
| Docker Swarm | Declarative services and manager/worker reconciliation. [E14] | Small-cluster ergonomics and simple bootstrap | Container-only assumptions and weaker portability contracts |
| Tekton | Pipeline/Task definitions and run resources for Kubernetes-native CI. [E25] | Optional PipelineRun controller over existing Jobs/Pods | A second scheduler or unqualified Tekton compatibility claim |
| OCI / Podman / containerd | Image/runtime boundaries and concrete local execution implementations. [E15, E16, E17] | Standards at the edge; proven execution engines where useful | Equating an OCI artifact with universal executable compatibility |
| FreeBSD OCI stack | Native jail-backed OCI execution through ocijail and related tooling. [E04] | Evaluate an adapter before writing another jail engine | Assuming Linux-style rootless support or identical network behavior |

**Decision:** Kubernetes vocabulary + Nomad-style control/execution separation + CUE/Pkl-style validation principles, implemented using Simple and SDN. HCL/YAML/JSON are optional import/export edges, not the native execution model.

### 3.2 HashiCorp architecture analysis

Nomad servers accept desired state and calculate placements. Clients advertise resources, attributes and drivers, register, heartbeat, receive allocations and report state. Nomad separates region state; intra-region servers coordinate through consensus, and placement proposals are optimistically concurrent with coordinated acceptance. [E08]

The useful structure for Simple is:

```text
Resource API -> controller -> scheduling work item -> placement proposal
                                                       |
                                          atomic validation/reservation
                                                       |
                                              committed PodBinding
                                                       |
Node watch -> local admission -> prepare/start -> observed status
```

Do not let a scheduling plugin directly start remote processes. Its result is a proposal, which the authority/state owner validates against current revisions, quotas, node capabilities and already committed reservations.

Nomad's task-driver interface is especially useful: drivers declare capabilities, fingerprint readiness, start tasks, return versioned recovery information, observe exits, stop tasks and separately destroy resources. Driver/client restart need not imply workload restart. [E09]

Translate those ideas into a `RuntimeProviderV1`; do not reproduce Nomad's Go object layouts or force its plugin transport into Simple. Simple's existing composition ABI remains authoritative.

### 3.3 HashiCorp product boundaries

Nomad is the scheduler/executor reference. Terraform supplies a useful plan/apply model for creating machines and installing the agent. Nomad can use native service discovery or optional Consul integration, so Consul must not become an unnecessary mandatory dependency of the Simple minimum profile. [E11, E18]

A credential-provider port may later integrate Vault; a discovery-provider port may integrate Consul. Neither belongs inside the minimal orchestration kernel. Learn architecture from published interfaces; importing third-party implementation code requires separate dependency/license review.

### 3.4 What to simplify initially

Use one logical cluster, one region, one active scheduling coordinator and a single durable store in the development profile. Define all state transitions as revision-checked operations so a replicated-store provider and multiple scheduler workers can be added without changing resource semantics. Multi-region federation and automatic topology expansion are later features, not prerequisites for three-host CI.

---

## 4. Native container reality and host support policy

### 4.1 Supported execution classes

| Class | Meaning | Example | Critical rule |
|---|---|---|---|
| `native-container` | OS container/jail isolation without a workload guest kernel | Linux OCI, Windows process, FreeBSD jail, qualified SimpleOS container | Requires certified isolation capabilities, not merely a process launcher |
| `native-sandbox` | Host-native process with a specific application sandbox | Admitted macOS App Sandbox application/helper | Not a substitute for missing container namespaces or arbitrary-code containment |
| `native-process` | Host-native execution with only advertised process controls | Trusted build/test helper | Explicit opt-in; do not schedule untrusted tenants here |
| `virtual-machine` | A workload executes using a guest kernel | Apple Linux VM, Windows Hyper-V isolation | Separate provider and explicit policy approval |

These are execution categories, not a total ranking of security strength. Isolation, privilege, networking, resource limits, and artifact compatibility are independent capability dimensions.

### 4.2 Host matrix

| Host | Native baseline | Provider path | Qualification and limits |
|---|---|---|---|
| Linux | Linux containers | OCI runtime adapter using crun/runc; optional containerd or Podman API provider | Probe namespaces, cgroup delegation, filesystem restrictions and networking; rootless is a separate capability profile. [E16] |
| Windows | Process-isolated Windows containers | containerd/runhcs/HCS integration first; optional direct typed HCS provider after parity | Windows image and host version must be compatible. Hyper-V and WSL2 are not native-lane substitutes. [E01, E05, E17, E19] |
| macOS | Host-native signed/sandboxed applications or explicitly trusted processes | Narrow native launch/sandbox helper using supported Apple facilities | No verified general-purpose Darwin OCI container equivalent. Apple's Linux containers are VM-based. [E02, E03] |
| FreeBSD, later | Jail-backed native containers | ocijail/Podman adapter, VNET/PF integration | Current handbook documents root-required Podman containers; resource support must be probed. [E04, E20] |
| SimpleOS, later | Existing Simple containers | Existing `ContainerRuntime` and managed-workload launcher | Require booted-kernel, cleanup, namespace and network evidence; Linux image compatibility is not implied. [R02, R03, R04] |

### 4.3 Windows design details

The first release target is a pinned Windows Server image/host combination from Microsoft's compatibility matrix. Windows client development support is separately qualified by edition, build and container image; it is not advertised as a universal production-host substitute. [E05]

Runtime setup must request **process isolation explicitly**. Record the effective HCS/runtime isolation mode in launch receipts, alongside the host build and image OS version. HNS networking is a distinct provider concern; the presence of a virtual switch does not itself establish that the workload has a separate guest kernel. [E01, E19, E21]

Use normalized lifecycle operations, not POSIX signal names as the mandatory contract. The Windows adapter translates graceful termination, forced termination, exit status, named-pipe I/O, filesystem ACLs and process resource limits into the portable API. Keep unsupported controls visible.

### 4.4 macOS design details

Two native lanes are useful and honest:

1. **Trusted native build/test worker:** runs a compiled Mach-O/Simple executable directly. The CI host is disposable or restored, and the workload is not advertised as a strongly isolated untrusted container.
2. **Qualified native application sandbox:** runs only admitted, correctly signed applications/helpers for which entitlements and inherited sandbox behavior have been tested. This is a capability-specific execution service, not a promise that any downloaded OCI image can be sandboxed.

Do not base a production guarantee on deprecated/private sandbox APIs. Reject `native-container` when no qualifying provider exists. A separate `apple-linux-vm` class can offer Linux-container compatibility without weakening or confusing the native lane. [E02, E03]

### 4.5 Portability must be explicit

A Windows image is not a Linux image with a different launcher. An OCI index can select platform-specific manifests, and image metadata includes OS/architecture information; this does not make their userspace ABIs identical. [E15]

Use the same source-level application protocol and orchestration contract, with separately built artifacts for Linux ELF, Windows PE, macOS Mach-O, FreeBSD ELF and SimpleOS-supported executable formats. Cross-OS rescheduling is permitted only when a matching artifact and required capabilities are available. A Pod never mixes host kernels.

---

## 5. Orchestration language: SDN plus ordinary Simple

### 5.1 Two authoring modes, one semantic model

| Mode | Allowed behavior | Output |
|---|---|---|
| `.sdn` resource file | Inert values, maps, sequences, source locations | Typed resource objects |
| `.spl` manifest builder | Ordinary Simple functions/library composition in an explicit build step | The same typed resource objects |
| Import adapter | Supported Kubernetes YAML/JSON or a later documented Nomad subset | The same objects, plus compatibility diagnostics |

The node agent does not parse source scripts. The scheduler does not evaluate arbitrary Simple. Admission operates on canonical, schema-versioned data. Script execution belongs in an explicit client/build environment with bounded resources and declared inputs.

### 5.2 API identity and compatibility

Use the proposed API group `orchestration.simple/v1alpha1` for Simple-native resources. Retain names such as `Deployment`, `Pod`, `Service`, `Node`, `Job`, `RuntimeClass`, `ConfigMap` and `Secret`.

A Kubernetes adapter may import `apps/v1`, core `v1`, and other explicitly supported groups. Export is allowed only when every relevant field and behavior can be represented. A resource requiring `macos`, `freebsd`, `simpleos`, an `ArtifactSet`, or endpoint-only networking is not silently presented as an upstream-compatible Pod.

Publish a versioned feature matrix: accepted exactly, translated with specified semantics, or rejected. Unknown fields are errors, not ignored extension points. Namespaced extension schemas are admitted only through registered providers and retain the same validation rules.

### 5.3 Example SDN resource

The schema and library names in this document are proposals. The following uses existing SDN-style mappings/sequences, not new grammar. `artifactSetRef` and `networkProfile` are explicitly Simple-native fields. The referenced fixture artifacts are produced by the CI build pipeline.

```sdn
apiVersion: orchestration.simple/v1alpha1
kind: Deployment
metadata:
    name: echo-linux
    namespace: ci
spec:
    replicas: 2
    selector:
        matchLabels: {app: echo-linux}
    template:
        metadata:
            labels: {app: echo-linux}
        spec:
            os: {name: linux}
            nodeSelector: {"kubernetes.io/os": linux}
            runtimeClassName: native-container
            networkProfile: endpoint-v1
            containers:
                - name: echo
                  artifactSetRef: ci-echo
                  args: ["--listen", "0.0.0.0:8080"]
                  ports: [{name: http, containerPort: 8080}]
                  resources:
                      requests: {cpu: "250m", memory: "64Mi"}
                      limits: {cpu: "1000m", memory: "256Mi"}
                  readinessProbe:
                      httpGet: {path: "/ready", port: http}
```

CI generates analogous Windows and macOS resources from the same builder. Windows uses `os.name: windows` and `native-container`; macOS uses `os.name: macos` and the explicitly selected `native-sandbox` or trusted `native-process` class. Do not make a resource with a strict container requirement match the macOS process lane.

### 5.4 Proposed Simple builder API

This is an API sketch, not currently implemented runnable code:

```simple
use std.orchestration.authoring.{BuildInputs, ResourceSet, ManifestError}
use std.orchestration.authoring.{TargetProfile, render_platforms}

fn manifest(inputs: BuildInputs) -> Result<ResourceSet, ManifestError>:
    render_platforms(
        inputs: inputs,
        template: "echo-linux.sdn",
        targets: [
            TargetProfile(os: "linux", runtime_class: "native-container"),
            TargetProfile(os: "windows", runtime_class: "native-container"),
            TargetProfile(os: "macos", runtime_class: "native-sandbox")
        ]
    )
```

Implement these as ordinary typed libraries. `render_platforms` reads only locked inputs, returns a validation error rather than applying anything, assigns distinct resource names, and updates selectors and template labels consistently. It rejects incompatible inherited fields. A helper that leaves Linux-only security settings on a Windows or macOS template is invalid. The macOS sandbox target is eligible only after that profile has been qualified; requesting it does not authorize fallback to an unsandboxed process.

### 5.5 Deterministic authoring and validation

A build locks all source modules, compiler/runtime artifacts, schemas and external inputs by digest. Environment variables, files, network data, time and randomness are forbidden by default in the hermetic builder profile; deliberately allowed inputs are captured in the lock. Execute the builder in a qualified isolated build environment, not with cluster credentials. Static typing alone does not prove effect-freedom.

Canonicalization must normalize resource quantities without floating-point ambiguity; CPU requests become integer millicores and memory becomes integer bytes. Map ordering is canonical. Array ordering remains semantic unless the schema defines a set/map list. Defaults are schema-versioned and included in the plan. Use a full cryptographic digest for security identities.

The strict SDN adapter rejects duplicate keys, unknown properties, invalid types, overflows, negative resources, selector/template disagreement, unresolved references, unsupported OS/runtime combinations, ambiguous artifact selection, and unbounded input depth/size. Preserve source spans for each rejection. The ordinary parser's last-wins behavior is never used as an orchestration merge policy. [R01]

### 5.6 Composition and overlays

Prefer typed Simple functions for reusable structure and a small explicit patch model for environment overrides. A patch names a resource UID/name, a schema path, an operation and a value; conflicting patches fail unless their order is explicitly declared. No implicit text substitution, ambient shell expansion, executable YAML tags, or hidden network fetches.

`null`, deletion and an omitted field are different operations. Secret references may be composed, but secret values are not inserted into logged manifests. A successful plan is an immutable artifact, not permission to bypass revalidation at apply time.

### 5.7 Proposed command surface

```text
simple orchestrate validate deployment.sdn
simple orchestrate compose manifest.spl --inputs inputs.sdn --out bundle.sdn
simple orchestrate plan bundle.sdn --out plan.sdn
simple orchestrate apply plan.sdn
simple orchestrate get pods --namespace ci
simple orchestrate rollout status deployment/echo-linux
simple orchestrate drain node/windows-1
simple container run local-pod.sdn
simple container inspect <id>
simple container stop <id>
```

These are proposed commands. `compose` is not `apply`. `plan` reports unsupported capabilities and placements without starting workloads. `apply` checks identity, authorization, schema, current revisions and plan validity before committing intent. Root `--help` and `--version` must not load runtime providers, scan devices or connect to a cluster.

---

## 6. Resource model and Kubernetes vocabulary

Kubernetes defines Pods as the co-located execution unit. Simple should preserve that fundamental meaning rather than scheduling each container independently. [E06]

| Resource | Simple semantics | Delivery stage |
|---|---|---|
| `Namespace` | Administrative scope, quotas and API authorization; not an OS namespace | Core |
| `Node` | Authenticated agent, boot identity, OS/ABI, available resources/capabilities | Core |
| `RuntimeClass` | Named provider policy and required execution/isolation capabilities | Core |
| `Pod` | Indivisible co-placement unit, one node/kernel, specified shared resources | Core |
| `Deployment` | Desired stateless replicas and rolling-update policy | Initial cluster |
| `ReplicaSet` | Owns the replica population of a particular Pod template revision | Initial cluster |
| `Job` | Finite work, completion/backoff policy; attempts may repeat | Initial cluster/CI |
| `DaemonSet` | One Pod on each eligible node; not the bootstrap mechanism for node agents | Initial cluster |
| `Service` | Stable logical service identity over ready endpoint sets | Initial cluster |
| `EndpointSlice` | Batched concrete ready endpoints and ownership | Initial cluster |
| `ConfigMap`, `Secret` | Versioned non-secret data and secret references with distinct access rules | Initial cluster |
| `CronJob` | Scheduled Jobs with explicit timezone/missed-run/concurrency policy | After Job durability |
| `NetworkPolicy` | Enforced traffic policy only when the network provider can fulfill it | Capability gated |
| `PV`, `PVC`, `StorageClass` | Storage identity, binding, topology and access modes | After ephemeral/local storage |
| `StatefulSet` | Stable identity/storage lifecycle and disruption semantics | After storage/fencing qualification |
| `ArtifactSet` | Simple extension: locked per-platform executable/image choices | Core authoring/CI |

An internal `PodBinding` carries the chosen node, attempt identity, resource reservation, artifact digests, provider generation and admission-policy revision. It is not a second user-facing synonym for a Kubernetes Job.

### 6.1 Common metadata and status

Every resource has API group/version/kind, namespace where applicable, name, UID, generation, resource version, labels, owner references and lifecycle state. Status includes observed generation, conditions, transition times and stable reason codes. Intent and observation have separate update paths and permissions.

The controller owns desired replica relationships; the scheduler owns placement proposals; the state owner commits reservations; the node agent owns reported local observations; the runtime provider owns actual execution handles. No component writes another component's authoritative facts directly.

### 6.2 Pod details and unsupported sharing

A Pod is co-scheduled as a unit, but shared PID, IPC, filesystem, or network behavior is independently specified and capability checked. The first portable endpoint profile need not support every Kubernetes Pod-sharing option. If an imported Pod relies on semantics the provider lacks, reject it.

Use one compatible OS/ABI for every container in a Pod. Platform alternatives are resolved for the whole Pod before committing placement. Init-container ordering, readiness/liveness probes, restart policy and termination grace periods must be defined independently; an exit code is not a readiness signal.

### 6.3 Update and deletion semantics

Use optimistic resource-version checks for writes. Controller retries are idempotent. A stale rollout cannot overwrite a newer template. Deletion first records intent, then drains service endpoints, terminates workloads and cleans owned resources before final completion. Finalizers are bounded/audited workflow ownership, not a mechanism for hiding permanent leaks; force deletion records abandoned resources and requires explicit authorization.

---

## 7. MDSOC++ application kernel and plugin architecture

### 7.1 Keep the three kernels separate

The orchestration application kernel owns orchestration invariants. The reusable kernel-plugin library owns provider composition and lifecycle. The host OS kernel owns process/container enforcement. Their authority must not be conflated.

```text
orchestration application kernel
  identity / authorization / revisions / ownership / committed state
                 |
  shared composition + bounded async kernel-plugin substrate
                 |
  typed policy, controller, scheduler, runtime and service providers
                 |
  SOSIX/common host contracts -> allowlisted platform bindings
                 |
  existing Linux / Windows / Darwin / FreeBSD / SimpleOS enforcement
```

Reuse `SimpleProviderQueryV1`, composition images, version negotiation, capability admission and provider-generation ownership. The existing fixed-width ABI is the foundation, not a reason to invent an orchestrator-specific loader. The reusable async layer is a shared prerequisite until it lands and passes its own gates. [R06, R07, R08]

### 7.2 Kernel versus plugins

| Component | Mandatory invariant owner | Replaceable behavior |
|---|---|---|
| Resource API | Object identity, schema version, authorization, revision checks | Frontend protocols and explicitly registered resource schemas |
| State/transaction boundary | Atomic reservation semantics, no unauthorized state transitions | Durable local or replicated store implementation |
| Reconciliation | Ownership rules, committed desired/observed separation | Deployment, Job, DaemonSet and later controllers |
| Scheduling | Hard capability/authority constraints and reservation checks | Filter/score policy, fairness, topology weighting |
| Node agent | Node identity, journal ownership, binding validity, cleanup accountability | Runtime/network/storage/device providers |
| Container core | Portable lifecycle, artifact identity, operation IDs, receipts | Native execution and snapshot mechanics |
| Networking | Endpoint ownership and capability requirements | Host routing, Pod networking, service proxy and discovery |
| Security | Trust roots, ceilings, deny-by-default checks | Optional external secret/discovery/policy integrations |
| Observability | Stable receipt and audit schema | Exporters, log sinks, optional detailed tracing |

A plugin can propose behavior but cannot disable the invariants that admit it. A scheduler scorer cannot turn an incompatible Windows image into a compatible one. A network adapter cannot satisfy an enforced-policy requirement merely by claiming a label.

### 7.3 MDSOC++ ownership rules

Each capsule has a manifest, typed ports, capability budget, lifecycle and one owner for mutable state. ECS/data-oriented tables are useful inside the local container world and scheduling indexes, but are not mandatory for every capsule. Parent/child resource ownership follows the existing MDSOC++ direction: no hidden global ownership and no shared mutable graph through arbitrary plugin pointers. [R07]

Use static/sealed composition for the minimum profile. Compile-time and composition-seal checks reject duplicate interface IDs, missing providers, ABI/version conflicts, cycles that violate initialization rules, capability excess and unsupported placements. Runtime-open providers are an explicit separate profile.

### 7.4 Placement and generation policy

Support one logical contract in these placements: statically linked, sealed separately packaged, approved native dynamic, and isolated worker process. SMF placement is not enabled merely because a manifest can be read; it requires actual code-execution, admission and recovery proof.

Resolve interfaces at admission/session creation and dispatch through dense slots afterward. Pin a provider generation while its operations, workload handles, buffers or callbacks remain live. Replacement uses `admit -> warm -> publish -> drain old -> retire`; rollback is allowed only with a compatible recovery schema. Incompatible upgrades drain workloads instead of guessing how to recover them.

An isolated provider process adds a measurable IPC boundary. Use it for untrusted extensions, privileged helpers, or crash-prone integrations, not for every small pure scheduling function. Static pure policy can remain a direct call.

### 7.5 Stable ABI and network wire are different contracts

Local ABI descriptors contain fixed-width scalars, byte-arena offsets and opaque process-local handles. Do not send `provider_context`, raw pointers, function addresses or local slot handles across the cluster network. [R06]

Network messages use an independently versioned canonical codec carrying resource UIDs, attempt IDs, node identity, revisions and immutable payload bytes. A node-local recovery record can contain opaque provider data encrypted/restricted on that node, but the control plane treats it as data with a declared schema version. Security decisions use full-width cryptographic digests, not truncated identity hints.

### 7.6 No-GC async and SOSIX integration

Consume the shared SOSIX/ring operation lifecycle rather than creating another Future, cancellation token or completion queue. [R09] The target invariant is:

```text
reserve -> commit -> submitted -> completion/cancel outcome -> retire
```

Timeout does not establish that the native operation stopped. A borrowed buffer, native handle or provider generation remains pinned until completion or an explicit abandonment protocol proves safe reclamation. Generational IDs must not wrap and alias live state.

Use bounded operation pools and ready/event rings. Saturation returns backpressure, not an unbounded queue allocation. Long-lived registries may grow through explicit admitted capacity changes; sealed critical profiles preallocate them. Blocking host APIs execute in bounded adapter workers and complete into the common ring; they must not block the control-plane event loop.

### 7.7 Proposed source layout

These are proposed additions/ownership locations, not claims that the files already exist:

```text
src/lib/common/contracts/orchestration/
  resource_v1.spl          # IDs, metadata, spec/status, revisions
  binding_v1.spl           # placement/reservation/attempt identity
  node_v1.spl              # capabilities and boot identity
  evidence_v1.spl          # test/launch/admission receipts
src/lib/common/contracts/container/
  runtime_v1.spl           # lifecycle and normalized errors
  artifact_v1.spl          # image/platform identity
  network_v1.spl
  storage_v1.spl

src/lib/nogc_async_mut/orchestration/
  kernel/                 # invariant owner; imports shared kernel-plugin
  controllers/
  scheduler/
  state/
  agent/
  authoring/              # build-time only; excluded from node runtime closure
src/lib/nogc_async_mut/container/
  core/                   # portable management and ownership
  image/                  # locked image/registry metadata and verification
  providers/linux/
  providers/windows/
  providers/macos/
  providers/freebsd/

src/os/services/container/
  ...existing files...    # retained during migration
  orchestrator_adapter.spl

src/app/orchestrator/     # CLI/control/agent compositions, no provider internals
config/orchestration/    # inert composition and deployment data
```

The exact library-family placement is finalized by the shared contracts owner before implementation. `src/lib/mdsocpp` remains a composition facade if the predecessor plan introduces it; it must not contain a second runtime. The SimpleOS adapter alone reaches SimpleOS kernel modules. Portable code reaches host services through shared SOSIX/contracts and approved provider boundaries.

---

## 8. Simple Container: common behavior, narrow host differences

### 8.1 What to share

Share resource identities, artifact selection, admission, lifecycle, attempts/retries, Pod ownership, journal formats, immutable metadata, log framing, status normalization, diagnostics, policy reasoning and test contracts. Share pure algorithms after confirming their actual semantics.

Do not share OS-specific syscall constants, POSIX path assumptions, signal names, ACL implementations, process handles or kernel namespace structures by disguising them as portable values. The provider converts a validated portable request to native operations and reports exactly what it enforced.

### 8.2 RuntimeProviderV1 operations

| Operation | Required meaning |
|---|---|
| `probe` | Report supported/healthy capabilities and real native dependencies |
| `validate` | Check one Pod against effective provider/node/policy capabilities without launch |
| `prepare_pod` | Reserve/recover local shared state, network and storage ownership |
| `create` | Materialize a non-running native workload or return an idempotent existing result |
| `start` | Start execution and return a recoverable, versioned native identity |
| `inspect` | Observe native state; never infer execution from model state alone |
| `wait` | Report real exit/termination or an explicitly typed observation failure |
| `stop` | Request graceful termination with a deadline, then forced termination if authorized |
| `destroy` | Remove owned execution resources after stop/exit or under explicit force rules |
| `recover` | Reattach using persistent identity, boot ID and versioned provider recovery data |
| `logs`, `stats` | Bounded framed output and capability-qualified resource observations |
| `exec`, `resize`, `signal` | Optional capabilities; absence is explicit |

The stop/destroy split and versioned recovery follow the useful Nomad driver pattern. [E09] The portable API should not require POSIX signals; graceful shutdown is semantic, while native-specific actions are optional typed extensions.

### 8.3 Crash-safe local lifecycle

The agent writes an intent/ownership record before a native side effect. Each operation is keyed by `(PodUID, attempt, providerGeneration, operationID)`. Retries after timeout or reconnect must find the original operation or report ambiguity; they must not casually create another workload.

Prepare/create/start form a recoverable saga, not a fictional cross-kernel transaction. Every completed step records the resources it owns and its cleanup action. If start fails after network or storage allocation, compensation cleans only those resources belonging to that attempt. Recovery distinguishes a stopped workload, an orphan still running, an unreachable runtime and a reused PID.

A raw PID is insufficient identity. Include native runtime/container identity and node boot ID; the provider must prove the recovered handle belongs to the expected attempt. A process that outlives a client/plugin restart is adopted only after that check.

### 8.4 Migrate the current SimpleOS manager without a rewrite

Keep `ContainerRuntime` and its hash/root/task checks at the SimpleOS boundary. Retain the manager's container and Pod model until its behavior has parity fixtures. Extract only pure IDs, lifecycle rules and policy normalization that truly apply across hosts; leave kernel namespace objects and scheduler authority local. [R02, R03]

The extraction sequence is: current behavior tests -> common typed projection -> SimpleOS adapter in shadow mode -> same tests against the projection -> optional cutover -> delete duplicate logic only after measured parity. Do not mechanically move the whole `src/os/services/container` tree into the standard library.

### 8.5 Image and artifact handling

`ArtifactSet` is a Simple-native, immutable mapping from platform and runtime requirements to a locked OCI image or supported native package. A workload specifies exactly one of `image` or `artifactSetRef`. Resolution produces a concrete image/package digest, executable entrypoint, OS/arch/ABI and provider requirement before launch.

Use OCI image indexes where they represent the artifacts correctly; use explicitly typed OCI artifacts or Simple package metadata where a native application package is not an OCI runnable container. Artifact distribution compatibility is not executable ABI compatibility. [E15]

Registry transport, digest verification, signatures/trust policy, extraction and snapshotting are separately testable. The existing OCI adapter validates normalized declarations but does not implement those operations. [R04]

### 8.6 Secure filesystem handling

Never treat string replacement of `/` with `\\` as a host port. Prefer native runtime/snapshot APIs for platform image layers. When Simple owns extraction, use native handle-relative operations and no-follow/reparse-safe traversal where available; enforce actual decompressed byte and file-count limits, not only manifest declarations.

Test path traversal, symlink/hardlink escape, extraction races, Windows drive-relative paths, UNC paths, alternate data streams, reserved names, reparse points, case-fold collisions, Unix mode/capability metadata and host-device entries. Refuse unsupported metadata rather than silently weakening restrictions. The current textual `contains("..")`/leading-slash checks are not a sufficient portable filesystem security boundary. [R04]

### 8.7 Local command and agent ownership

`simple container` should work without a cluster. It calls the same common core and selected provider. For cluster-managed resources, it must not become a bypass around node authorization: local inspection is permissioned, and mutating cluster-owned resources requires an explicit administrative action recorded as drift or override.

Cluster mode necessarily has a node agent. Local mode may use per-workload monitors/short-lived commands where a provider supports them; do not force a root daemon into every local use merely to imitate the cluster architecture.

---

## 9. Distributed control plane and failure semantics

### 9.1 Submission to execution

The API validates and stores desired resources. Controllers reconcile desired replicas and emit pending Pods. A scheduler reads a coherent state revision, filters for artifact/runtime/security compatibility, scores candidates, and proposes a binding. The state owner atomically verifies revisions and reserves resources before publishing the binding. The node agent then revalidates local prerequisites, starts the workload and reports actual observations.

This retains the useful Nomad distinction between computing placement and safely accepting it, without requiring the first release to parallelize every scheduling worker. [E08]

### 9.2 Hard constraints before scoring

Hard filters include authenticated node eligibility, OS/architecture/ABI, Windows image compatibility, runtime class, resource requests, local resource reservations, network/storage capabilities, device requirements, policy ceilings, topology and taints/tolerations where implemented. Missing required enforcement is an admission failure, not a low scheduler score.

Soft scoring can consider remaining resources, image locality, measured startup cost, topology spread, affinity, data locality and fairness. Start with deterministic integer scores and stable tie-breaking. Store the reason for rejection or placement in a receipt so humans and agents can inspect it.

### 9.3 State providers and availability

The development profile uses a single durable store with a write-ahead journal and tested crash recovery. It is not highly available.

The production profile requires a qualified replicated transactional store. Integrating an established external store through a narrow provider is preferable to writing a new consensus implementation during the host-port project. A future Simple-owned implementation must pass the same durability, partition and linearizability tests before substitution. Nomad's consensus architecture is a useful reference, not a shortcut around these tests. [E22]

Start with three voters in distinct failure domains for the production qualification topology; a five-voter option is a separate tested configuration. Without quorum, do not acknowledge new committed placements. Node agents follow the configured disconnected-workload policy while existing tasks may continue.

### 9.4 Heartbeats are not fencing

A missed heartbeat means the controller cannot establish liveness; it does not prove the workload has stopped. For a stateless replicated service, replacement may be acceptable under a documented overlap policy. For an exclusive writer, payment job or device owner, replacement requires an enforceable fence at the protected resource or another proof that the old owner cannot continue.

A larger epoch in a controller record is not sufficient if an old process can still write to the database/disk/device. Storage or service authorization must reject stale epochs, or the old node must be fenced before reassignment. Test the case where control traffic is partitioned but the old workload can still reach its data service.

### 9.5 Job and retry semantics

A Job has stable logical identity and separately identified attempts. Execution and observation can be retried. Do not claim exactly-once external effects; applications need idempotency keys or transactional fencing at the effect boundary. Distinguish node loss, runtime loss, execution failure, cancellation and successful completion.

Persist controller decisions and observations so restarts do not reset backoff, recreate completed Jobs or erase evidence. Watch clients handle revision compaction by taking a new snapshot and reconciling; no assumption of an infinite lossless event stream.

### 9.6 Upgrades, drain and recovery

Node drain stops new admissions, removes ready endpoints as appropriate, honors disruption policy, and terminates/migrates only where supported. Resource migration means replacement with compatible artifacts and storage, not transparent live process migration.

A provider upgrade checks both ABI compatibility and recovery-record compatibility. Maintain a known-good rollback generation. Test controller crash, node-agent crash, provider crash and host reboot independently; they have different recovery meanings.

---

## 10. Networking and storage with minimum host variance

### 10.1 Two network profiles

| Profile | Common guarantee | Host requirement | Compatibility claim |
|---|---|---|---|
| `endpoint-v1` | Owned reachable endpoints, named ports, readiness and discovery; optional shared service proxy | Real host networking and provider-owned port allocation | Simple-native portable profile; not a claim of full Kubernetes Pod networking |
| `pod-ip-v1` | Per-Pod addressability and specified isolation/sharing behavior | Qualified namespace/HNS/VNET/SimpleOS network provider and routing | Kubernetes-like subset only where the tested semantics match |

Start cross-host CI with `endpoint-v1`. Each workload advertises an owned reachable endpoint, not just `127.0.0.1`. A common discovery/service layer selects ready backends. Host adapters implement port publication and endpoint ownership. This enables real Linux/Windows/macOS communication before a full multi-OS overlay exists.

Then qualify stronger Pod networking for Linux, Windows, FreeBSD and SimpleOS. macOS native processes do not gain a Pod network namespace merely because a service proxy exists. A VM provider may offer guest Linux Pod networking, but its runtime class remains a VM.

### 10.2 Provider boundaries

`NetworkProviderV1` handles reserve/create/attach/inspect/detach/destroy/recover, with endpoint generation and ownership. Linux can use qualified CNI or another native network backend; Windows uses HNS-related APIs; FreeBSD uses VNET/PF plumbing; SimpleOS uses its own network service; macOS native mode uses explicitly supported host-network operations. [E21, E04]

Keep service discovery, EndpointSlice updates, readiness selection and protocol-independent endpoint records common. Keep OS firewall, route, NAT and virtual-interface operations inside providers. Do not put every application packet through the orchestration control plane.

### 10.3 NetworkPolicy is an enforcement contract

A `NetworkPolicy` is admitted only if all required ingress/egress paths can be enforced for the selected profile. Filtering only the service proxy is not sufficient when direct destination IP access can bypass it. Test both permitted and prohibited traffic, including direct addressing and DNS resolution paths.

For an unsupported native macOS policy, reject the deployment or require an explicit different profile. Application-level brokered sockets may be a future restricted Simple capability, but must not be mislabeled as arbitrary-process network isolation.

### 10.4 Service behavior

A Service selects ready owned endpoints. Readiness failure removes a backend; liveness policy may restart it, but those are separate decisions. Port allocation is conflict-checked and recovered after agent restart. Publish service names through a selected DNS/discovery provider and document name/TTL/update behavior.

In endpoint mode, DNS SRV or a portable service proxy can expose host/port endpoints. Do not export a Kubernetes `ClusterIP` object unless actual virtual-IP semantics are implemented. TLS/mTLS transport policy is distinct from OS packet isolation.

### 10.5 Storage roadmap

Initially support read-only image/package content, per-attempt ephemeral writable storage and explicitly mounted local persistent volumes. Separate generic ownership and artifact-cache rules from snapshot mechanics.

Later add PV/PVC/StorageClass with topology and access modes. A local volume cannot simply follow a Pod to another host. Single-writer failover requires storage fencing. CSI compatibility, distributed volumes, live migration and cross-OS filesystem metadata conversion are separate projects with their own qualification.

---

## 11. Security, resource enforcement and observability

### 11.1 Authority model

Authenticate users/controllers/nodes with distinct identities. Use authenticated encrypted transport and short-lived node/workload credentials. Namespace-scoped authorization does not give a workload access to node-admin operations. Privileged host helpers accept only typed approved requests, not arbitrary shell commands.

A node reports capability evidence under its authenticated identity. Ordinary workload-supplied labels cannot assert kernel isolation, secure boot, runtime health or image compatibility. A compromised node is outside the guarantee of its own self-report; stronger attestation is an optional later trust profile, not assumed.

Secrets are referenced by identifier/version and materialized only for authorized workloads. Do not log secret values, environment dumps or unredacted network captures. Registry credentials and CI lab credentials are distinct from production cluster credentials.

### 11.1a Native isolation and the threat model

Native-container support is not a blanket hostile-multitenancy guarantee. Microsoft explicitly distinguishes process-isolated Windows containers from the stronger hypervisor-isolated boundary and advises against process isolation for hostile tenants. [E26]

The native first-cohort CI profile therefore runs admitted trusted code on isolated test infrastructure. A policy requiring stronger separation must select a qualifying VM/dedicated-host profile explicitly or reject placement. It must not silently relax the threat model to preserve the no-VM preference. Dedicated physical hosts remain an option when workloads must stay native while tenants cannot share a kernel.

### 11.2 Resources are not interchangeable

Represent CPU requests in millicores and memory in bytes, but separately track reservation, scheduling weight, hard ceiling and observed usage. A host that only provides a scheduling weight must not claim a hard CPU quota. Process limits, I/O quotas, memory ceilings and device restrictions require provider-specific positive and negative tests.

Reserve capacity for the node agent, host OS and privileged helpers. Hard limits are admitted only where enforcement exists. A macOS native process lane may offer observations and placement reservations without all Linux-style hard limits; those limitations remain explicit.

### 11.3 Diagnostics and evidence

Every failed admission names the resource path, required capability, observed provider support and remediation category. Every launch receipt includes Pod UID, attempt, node/boot ID, effective runtime/isolation mode, concrete image/package digest, provider generation and native identity.

Measure controller latency, queue occupancy, reconciliation retries, placement conflicts, image pull/unpack time, runtime start latency, endpoint readiness, resident memory, native handle counts, orphan count and cleanup failures. Detailed tracing is optional; lightweight counters and error receipts remain available.

### 11.4 Performance gates, not invented numbers

No memory/startup/throughput measurements were taken in this review. Freeze numerical budgets only after a real baseline exists. Initial structural gates are: no unbounded hot-path queue; no per-event provider lookup; no unexpected provider imports; no compilation on production startup; no leaked native resources; no spin-based waits; and no extra interpreter/compiler closure in the agent.

Memory should be explainable as base runtime plus admitted node/Pod records, bounded operations, artifact metadata, active logs and provider state. Measure static versus worker/dynamic placement on the same workloads rather than promising zero overhead for every placement.

---

## 12. Build orchestration using the same language and execution model

### 12.1 CI is a controller plugin, not a second scheduler

Add an optional CI capsule using Simple-native `Pipeline` and `PipelineRun` resources. This borrows the useful separation of reusable pipeline definitions and individual executions from Tekton; it does not claim Tekton API compatibility. Tekton models CI/CD with Kubernetes custom resources and executes its task work through Pods. [E25]

In Simple, a `PipelineRun` expands into ordinary `Job` resources with declared dependencies. The existing Job controller, scheduler, node agent, runtime and artifact store remain the execution path. No separate CI process runner is permitted to bypass runtime-class admission.

```text
Pipeline definition + locked inputs
              |
          PipelineRun
              |
      build-linux   build-windows   build-macos
              \          |          /
            verify and publish ArtifactSet
                        |
              local runtime conformance
                        |
             mixed-host network qualification
                        |
                evidence aggregation
```

### 12.2 Proposed SDN pipeline

This is a design fixture with proposed fields and job templates, not a workflow executable by the current repository:

```sdn
apiVersion: ci.simple/v1alpha1
kind: Pipeline
metadata:
    name: orchestrator-qualification
spec:
    jobs:
        - name: build-linux
          jobTemplateRef: build-simple-linux
        - name: build-windows
          jobTemplateRef: build-simple-windows
        - name: build-macos
          jobTemplateRef: build-simple-macos
        - name: publish-artifacts
          runAfter: [build-linux, build-windows, build-macos]
          jobTemplateRef: seal-platform-artifacts
        - name: mixed-network
          runAfter: [publish-artifacts]
          jobTemplateRef: real-three-os-network
        - name: evidence
          runAfter: [mixed-network]
          runPolicy: always
          jobTemplateRef: aggregate-required-evidence
```

Each build uses an exact source revision and toolchain lock. Job templates specify native OS, runtime class, resource budget, privileges, workspace mounts, artifact outputs and timeout policy. Native macOS build tools may require the trusted-native lane; the pipeline must state that instead of inventing a generic macOS container.

The controller validates DAG acyclicity, output/input compatibility, missing templates, attempts and cancellation. `runPolicy: always` collects diagnostics after failure but does not convert failure into success. A failed build blocks dependent execution while independent builds continue.

### 12.3 Artifact/cache policy

Cache keys include source/tree digest, dependencies, compiler/toolchain, target OS/architecture/ABI, build options and relevant environment lock. Artifact provenance records the generating Job/attempt. Secrets never enter cache keys or reusable outputs in plaintext.

A cached binary is not cached network evidence. Fresh cross-host qualification is required for a new runtime/provider/OS-image combination. Restore only trusted immutable caches; do not let an untrusted PR overwrite the cache used by protected release jobs.

### 12.4 Avoid self-certification and bootstrap cycles

An independently trusted coordinator installs candidate binaries and verifies their behavior. The candidate orchestrator may schedule the test workload, but it cannot be the sole authority deciding whether its own assertions passed. Capture native runtime evidence and externally observed network results.

Until the Pipeline controller exists, a conventional trusted CI harness runs the same versioned test plan. After it exists, run both paths against the same evidence schema before switching the default. Keep a recovery path that does not depend on a healthy candidate orchestrator.

---

## 13. CI architecture: real execution, real networking, truthful results

### 13.1 Evidence levels

| Level | What is established | What is not established |
|---|---|---|
| Source/format check | Syntax or structural policy is valid | Buildability or execution |
| Build | Target executable was produced | Executable startup or isolation |
| Discovery | Tests can be enumerated | Test bodies ran |
| Local execution | Test bodies and target process ran | Real container enforcement unless asserted |
| Native runtime conformance | Real native workload and required enforcement were observed | Cross-host networking |
| Multi-host network | Separate hosts exchanged workload-generated traffic | HA or storage fencing |
| Failure/security qualification | Specified fault and isolation scenarios passed | Untested platforms/features |

Preserve existing discovery jobs, but label them honestly. The inspected `--list` invocations do not count toward execution coverage. [R10]

### 13.2 First-cohort topology

Use simultaneously reachable nodes and one external coordinator:

| Node role | Minimum purpose |
|---|---|
| Linux L1 and L2 | Native Linux containers, same-OS failover and cleanup |
| Windows W1 and W2 | Compatible native Windows process-container pair; same-OS failover |
| macOS M1 | Real native macOS build/workload/sandbox qualification |
| Coordinator C | Provisioning, artifact locks, native evidence collection and independent verdict |

A single node per OS is enough for the six mixed-OS traffic paths, but not for same-OS failover. Add M2 before claiming macOS failover qualification. For HA testing, use three controller/store voters in distinct failure domains; running three voters on the same host is not host-failure evidence.

Standard hosted CI can supply build/unit jobs, but three disconnected matrix jobs are not a live cluster. A protected lab or an explicitly connected disposable test topology is required. GitHub Actions supports conventional Linux/Windows/macOS runners; use a coordinator-driven target harness for FreeBSD/SimpleOS instead of assuming an official native Actions runner for them. [E23]

### 13.3 Required directed network matrix

| Source workload | Target workload | Initial required result |
|---|---|---|
| Linux | Windows | Authenticated request/response on real native workloads |
| Windows | Linux | Same, reverse direction independently tested |
| Linux | macOS | Native Linux container to actual Darwin workload |
| macOS | Linux | Actual Darwin workload to native Linux container |
| Windows | macOS | Native Windows process container to actual Darwin workload |
| macOS | Windows | Actual Darwin workload to native Windows process container |

Each direction includes TCP/HTTP, TLS or mTLS, UDP where required by the declared profile, DNS/service discovery and readiness-driven endpoint changes. IPv6 is required only for the advertised IPv6 profile; unavailable IPv6 is not silently counted as tested. Add all new directed pairs as FreeBSD and SimpleOS enter the cohort: five OS classes imply twenty directed cross-class pairs.

### 13.4 Proving traffic came from the workload

The coordinator issues a fresh nonce and expected destination identity. A client inside the source workload contacts the destination workload and obtains a signed/authenticated response containing the nonce, destination Pod UID/attempt, artifact identity and protocol result. Correlate these with trusted node/runtime records and independent network observations; do not trust a self-reported OS string alone.

Reject evidence produced only by SSH on the host, localhost loopback, a simulator, a mocked provider, or a proxy that substitutes its own echo response. A proxy carrying actual workload traffic is valid only when the tested profile explicitly uses it and endpoint ownership is proven.

### 13.5 Native-execution evidence by OS

| Target | Required evidence |
|---|---|
| Linux | Runtime/container identity, host/kernel relation, namespace identifiers, cgroup/resource placement, observed workload PID and traffic |
| Windows | Effective process-isolation configuration, HCS/runtime compute identity, host/image build compatibility, real workload observation and traffic |
| macOS | Actual Mach-O/Simple workload under Darwin, declared process/sandbox class, signed-helper/entitlement checks where claimed, real traffic |
| FreeBSD | Jail ID and runtime identity, VNET/endpoint ownership, resource enforcement where requested, real traffic |
| SimpleOS | Boot identity, actual scheduler task and namespace/capability ownership, live exit cleanup, real packets through a real network path |

For SimpleOS, multiple QEMU guests may be a valid guest-kernel qualification environment; record that fact. They are not bare-metal proof. A later hardware lane covers real device behavior. A Linux process pretending to be a SimpleOS agent does not qualify.

### 13.6 Fault matrix

Test node-agent crash, provider crash, workload crash, host reboot, controller restart, controller leader loss, quorum loss, stale watch/reconnect, delayed completion, duplicate launch request, lost launch response, image download interruption, disk-full during journal commit, port conflict and cancellation during startup.

Network faults must distinguish control-plane partition from data-plane failure. Include a partitioned old writer that retains access to its data service; replacement must be fenced or explicitly blocked. Include service drain during active connections, readiness flaps, certificate rotation and expired/revoked identities.

### 13.7 Result vocabulary

| Verdict | Meaning |
|---|---|
| `PASS` | All required assertions for this test ran and succeeded with valid evidence |
| `FAIL` | An assertion failed or execution produced an unexpected error |
| `BLOCKED` | Required runtime, compiler, machine, permission or artifact was unavailable |
| `UNSUPPORTED` | The capability is deliberately absent in this profile and is documented |
| `NOT_RUN` | The test was not attempted |

An **expected rejection** test can pass by verifying the correct rejection, while the underlying feature remains unsupported. Thus `macOS rejects native-container` may be PASS, but `native-container on macOS` remains UNSUPPORTED. Missing required evidence never yields a green release gate. Optional unsupported capabilities remain outside the claimed support profile rather than blocking an unrelated valid profile.

### 13.8 Proposed CI workflow split

| Proposed workflow | Purpose | Environment |
|---|---|---|
| `orchestrator-build.yml` | Build/execute parser, contracts and pure controller tests on Linux/Windows/macOS | Disposable unprivileged runners |
| `container-native-conformance.yml` | Real local runtime/security/resource tests | Protected disposable native hosts |
| `orchestrator-network-e2e.yml` | One live coordinated heterogeneous cluster | Protected connected lab |
| `orchestrator-failure-e2e.yml` | Partitions, reboot, recovery, HA and fences | Isolated fault-injection lab |
| `orchestrator-evidence.yml` | Validate expected test IDs and required evidence; publish support matrix | Least-privilege trusted aggregator |
| `orchestrator-later-hosts.yml` | FreeBSD and SimpleOS target qualification | Coordinator plus real target nodes/guests |

Use `fail-fast: false` for independent host builds. Dependent jobs must preserve the difference between blocked and failed. The final aggregator runs even after failures and checks the expected matrix against delivered evidence.

### 13.9 CI trust boundary

Do not execute untrusted public-PR code on persistent privileged runners connected to valuable networks. Use disposable build runners for untrusted changes; require protected approval/commit admission before launching privileged network and runtime tests. GitHub explicitly warns about persistent self-hosted-runner compromise and recommends careful isolation; one-job registration does not by itself sanitize reused hardware. [E24]

Use ephemeral credentials, pinned actions/dependencies, least-privilege tokens, dedicated test VLANs or equivalent isolation, and teardown plus out-of-band cleanup. Never expose a container runtime admin socket or HCS helper as an unauthenticated network service. Network captures and diagnostic bundles must be redacted and access controlled.

### 13.10 Evidence bundle schema

Every run produces:

```text
run ID and test-plan digest
source revision and compiler/runtime digests
per-host OS/build/architecture/ABI and boot identity
provider versions, ABI digests and effective runtime class
resolved image/package digests and compatibility decision
requested and effective capabilities/resource limits
actual commands, execution timestamps and raw exit records
Pod/attempt/native runtime identities
network challenge transcript and redacted native/network evidence
per-test assertions, verdict and reason
cleanup inventory and remaining-resource report
```

A signed evidence index binds artifacts to test IDs. Source scans, simulated tests and test enumeration get separate labels. The aggregator cannot infer an execution PASS from an exit-zero process that discovered no tests.

---

## 14. Acceptance test catalog

These test identifiers are proposed acceptance contracts; none is reported as executed in this review.

| ID | Required test | Pass criterion |
|---|---|---|
| LANG-001 | SDN scalar/map/sequence round-trip | Canonical meaning and source diagnostics preserved |
| LANG-002 | Duplicate keys | Admission rejects every duplicate with a source location |
| LANG-003 | Unknown and mistyped fields | Exact schema-path rejection, no silent dropping |
| LANG-004 | Resource quantity overflow | Checked failure, no wrap/truncation |
| LANG-005 | SDN versus Simple builder | Same declared inputs produce the same canonical resources |
| LANG-006 | Hermetic builder | Undeclared external inputs denied or explicitly captured |
| LANG-007 | Selector/template mismatch | Invalid Deployment rejected |
| LANG-008 | Compatibility import/export | Supported subset round-trips; unsupported semantics reject |
| PLUG-001 | Missing/version-mismatched provider | Admission fails before native side effects |
| PLUG-002 | Stable ABI boundary | No private object/pointer leakage; size/version checks |
| PLUG-003 | Generation pinning | Old generation cannot unload while handles/operations live |
| PLUG-004 | Late completion after timeout | No reused-slot or freed-buffer access |
| PLUG-005 | Queue saturation | Bounded backpressure; no unbounded memory growth |
| PLUG-006 | Import closure | Portable binaries do not pull unrelated OS kernel/providers |
| CTR-001 | Create/start/inspect | Real native execution observed, not model-only running state |
| CTR-002 | Duplicate launch/retry | One intended workload attempt, recoverable operation result |
| CTR-003 | Agent/provider crash | Correct adoption or explicit lost-state report, no arbitrary PID adoption |
| CTR-004 | Stop versus destroy | Correct exit observation and complete owned-resource cleanup |
| CTR-005 | Image mismatch/corruption | Rejected before execution |
| CTR-006 | Malicious layer paths/metadata | No escape, denied metadata or unsafe extraction |
| CTR-007 | Limits | Requested supported hard limits actually constrain workload |
| CTR-008 | Filesystem/process boundary | Workload cannot access prohibited host/sibling resources |
| WIN-001 | Native process mode | Effective isolation is process, not Hyper-V/WSL |
| WIN-002 | Host/image compatibility | Allowed pair runs; disallowed pair rejects without VM fallback |
| MAC-001 | Native execution | Workload runs under Darwin, not a Linux guest |
| MAC-002 | Sandbox restrictions | Each claimed restriction is independently tested |
| MAC-003 | Unsupported native container | Correct explicit rejection, not process fallback |
| BSD-001 | Native jail identity | Runtime workload is an actual owned jail |
| BSD-002 | VNET/PF/resource controls | Requested qualified capabilities enforced |
| SOS-001 | Actual SimpleOS task launch | Real booted scheduler/task evidence |
| SOS-002 | Authority teardown | Leader/worker resources revoked after actual exit |
| NET-001 | Six directed first-cohort paths | All required real workload exchanges pass |
| NET-002 | Discovery | Service name resolves to eligible ready owned endpoints |
| NET-003 | Readiness/drain | Endpoint set tracks readiness and drain policy |
| NET-004 | Port conflict/recovery | No duplicate ownership or leaked reservation |
| NET-005 | Traffic policy | Both allowed traffic and bypass attempts tested |
| NET-006 | IPv6 profile | All advertised IPv6 paths work, or profile is not advertised |
| CTRL-001 | Rolling update | New revision converges under declared availability policy |
| CTRL-002 | Node drain | No new admissions; correct disruption/cleanup behavior |
| CTRL-003 | Scheduler conflict | Concurrent proposals cannot over-reserve resources |
| CTRL-004 | Watch reconnect/compaction | Snapshot/resync converges without duplicate effects |
| CTRL-005 | Job retries | Attempts tracked; completed state survives restart |
| HA-001 | Leader loss | Committed state preserved, new leader makes safe progress |
| HA-002 | Quorum loss | No false success for uncommitted placements |
| HA-003 | Partitioned exclusive writer | Fence enforced or replacement blocked |
| HA-004 | Journal crash/disk-full | No lost committed ownership or hidden orphan |
| SEC-001 | Invalid node identity | Join and privileged operations denied |
| SEC-002 | Capability amplification | Workload/provider cannot exceed admitted authority |
| SEC-003 | Secret handling | No unauthorized materialization or log leakage |
| SEC-004 | Threat-model admission | Hostile-tenant requirement cannot select an insufficient shared-kernel profile |
| CI-001 | No-tests/discovery-only | Execution gate refuses fabricated PASS |
| CI-002 | Incomplete host matrix | Missing required rows block release profile |
| CI-003 | Cleanup failure | Leak is a failed qualification, not discarded warning |
| PERF-001 | Minimal startup/import closure | Measured baseline and agreed budget preserved |
| PERF-002 | Sustained workload churn | Bounded memory/handles and no unbounded queues |

---

## 15. Porting roadmap and milestone gates

### 15.1 Port every role, but qualify them independently

| Host | CLI/authoring | Node agent/common core | Native runtime | Control-plane hosting |
|---|---|---|---|---|
| Linux | First cohort | First cohort | First cohort OCI | Initial production reference |
| Windows | First cohort | First cohort | First cohort process containers | Same source; qualify filesystem/TLS/store/process behavior before production claim |
| macOS | First cohort | First cohort | Native sandbox/process profile | Same source; development hosting first, production durability separately qualified |
| FreeBSD | Later cohort | Later cohort | Jail/ocijail | Later, after store/SOSIX/network qualification |
| SimpleOS | Later cohort | Later cohort | Existing Simple container adapter | Later, conditional on durable storage, TLS, networking and runtime readiness |

The first portable control-plane application may use an external qualified state service; that avoids requiring an embedded consensus port on every host. A host's ability to run the node agent is independent of its ability to host a production control-plane voter.

### 15.2 Milestones

| Milestone | Deliverable | Exit gate | Difficulty/risk |
|---|---|---|---|
| M0 | Snapshot, runnable toolchain inventory, shared contracts readiness | Evidence distinguishes real executable/shim/absent provider | Medium; repository/runtime dependencies |
| M1 | Strict SDN resource schemas, canonical IR, ordinary Simple builder | LANG-001..008; no new grammar/parser fork | Medium |
| M2 | Shared runtime interfaces, static composition, local journal, controller model | PLUG tests and crash-model tests; no production execution claims | Medium-high |
| M3 | Linux real local vertical slice | CTR native/cleanup/security tests on L1/L2 | High security relevance |
| M4 | Windows native process provider | WIN-001/002 plus common CTR tests | High: host/image and native API differences |
| M5 | macOS native workload/sandbox lane | MAC-001..003 plus honest capability negatives | High restrictions; narrower than a container port |
| M6 | Deployment/Job/Service controllers and first-cohort mixed network | Six directed paths, readiness, drain, recovery, CI evidence | High distributed/network work |
| M7 | Replicated-state production profile and failure/security suite | HA, SEC, sustained churn; no false guarantees | Very high; production gate |
| M8 | FreeBSD native jail/ocijail integration | BSD suite and all new directed pairs | High; reuse native stack |
| M9 | SimpleOS integration and real booted-network tests | SOS suite and all new directed pairs | High; depends on actual kernel/network capabilities |
| M10 | Optional profiles: full Pod networking, stateful storage, VM adapters, advanced devices | Separate feature conformance matrix | Separate scope, not hidden in first release |

Windows/macOS provider work can proceed in parallel with Linux after contracts freeze; the order above describes qualification dependencies, not a demand to serialize all development. FreeBSD/SimpleOS adapters remain architecturally planned from M1 without blocking the first cohort.

### 15.3 Linux port procedure

Package the agent and narrow runtime helper. Probe the selected OCI runtime, user/rootless delegation, namespaces, cgroup limits and network provider. Launch the locked echo fixture, verify native identities, impose limits, test prohibited filesystem/process access, then force crashes and verify cleanup. Use an existing runtime before considering a Simple-written syscall-level replacement. Replacing a mature security-sensitive runtime is a separate parity project.

### 15.4 Windows port procedure

Produce a working Windows executable and validate FFI/ABI/error paths before declaring the port. Select a known allowed Windows host/base-image combination. Integrate containerd/runhcs/HCS without shell-output scraping; keep a typed direct-HCS provider as an optional later reduction of dependencies. Implement HNS endpoint ownership, Windows image-layer handling, durable journal operations, process I/O and graceful/forced termination. [E17, E19, E21]

Run explicit negative compatibility tests and prove no automatic Hyper-V fallback. Test reboot/recovery on the exact OS build. Add a second qualified host/base-image series separately rather than treating all Windows releases as one target.

### 15.5 macOS port procedure

First prove the native executable, event loop, transport, journal and lifecycle on a real macOS target. Add the trusted native build worker. Then qualify the supported signed application/helper sandbox profile and its exact filesystem/network/resource capabilities. Keep signing/entitlement requirements in the artifact metadata and admission policy. Do not broaden the profile from one successful sample to arbitrary untrusted code.

Native network CI can begin in the explicitly trusted lane while sandbox support is developed, but its reports must state the actual runtime class. Apple Linux VM support, when added, is a distinct compatibility lane.

### 15.6 FreeBSD port procedure

Use the current jail-backed OCI tooling as the reference integration. Probe privilege requirements, runtime availability, ZFS/VFS choices, VNET/PF networking and resource controls. The current handbook's root requirement must be reflected in the helper trust model. [E04]

Use an authenticated coordinator to deploy/run the node binary and collect jail/native evidence. Test jail cleanup after agent/provider crash and reboot. Add FreeBSD-origin and FreeBSD-destination traffic tests against each existing OS.

### 15.7 SimpleOS port procedure

Reuse `ContainerRuntime` and its managed-workload security seam. Bind common resource/admission records to SimpleOS policies without weakening image/root checks. Connect real agent transport, timers, durable state and logging through the canonical SOSIX operations. [R03, R09]

Start with booted SimpleOS guests connected to the qualification network; verify actual packets and scheduler transitions. Then add board/bare-metal tests. If TLS, persistent storage or the network stack is not available, mark the relevant role BLOCKED rather than substituting a host process and reporting a SimpleOS pass.

---

## 16. Parallel-agent work breakdown and ownership

| Workstream | Primary ownership | Required partner | Deliverable and boundary |
|---|---|---|---|
| A0 Contracts/integration | Common resource/runtime/network/evidence interfaces | Security and every host owner | Sole editor of stable V1 layouts; publish fixtures and change log |
| A1 SDN/authoring | Strict adapter, schemas, Simple builders, canonicalization | Existing SDN/compiler owner | No independent parser or new grammar |
| A2 Shared kernel-plugin integration | Composition and async lifecycle adapter | Existing kernel-plugin lane owner | Consume/fix shared substrate, never clone it |
| A3 Control plane | Controllers, revisions, scheduling proposals, state provider | Distributed-systems/test owner | No native host execution calls |
| A4 Common container | Lifecycle/journal/artifact selection/receipts | Existing SimpleOS container owner | Pure extraction with parity, no mechanical OS-tree move |
| A5 Linux | Linux runtime/network/storage leaves | Security + common-container owner | Real native evidence and failure cleanup |
| A6 Windows | HCS/runhcs/HNS, compatibility, native I/O | Windows layer expert + container feature expert | No VM fallback; no POSIX path/signal assumptions |
| A7 macOS | Native launch/sandbox/signing integration | Apple platform expert + policy owner | Explicit supported/unsupported capability matrix |
| A8 Networking/storage | Common endpoint/discovery contracts and host adapters | Every host owner | Common behavior with native enforcement leaves |
| A9 CI/evidence | External coordinator, Job/Pipeline controller, test catalog | Security + release owner | Executed assertions, full required matrix, clean teardown |
| A10 FreeBSD | Jail/ocijail/VNET/PF port | Networking/container owners | Later-host gates |
| A11 SimpleOS | Native container/SOSIX/boot/network adapter | Kernel/driver owners | Keep kernel enforcement MDSOC-only |

Pair feature and layer expertise where possible: a container-lifecycle reviewer plus an OS specialist, or a scheduling reviewer plus a state/consensus specialist. Do not let every parallel agent edit shared ABI files or generated registration tables.

### 16.1 Dependency and merge rules

A0 freezes contracts and golden data first. A1/A2/A4 can then progress in parallel; A3 and host work use those contracts. Runtime/network/security test fixtures are reviewed before the implementation they judge. A9 creates the independent harness early, not at the end.

Each workstream uses a separate branch/worktree. Commit file moves/renames separately from semantic changes. Keep existing paths via adapters until equivalence passes. Generated files are regenerated by the owner, not independently patched. A revision mismatch in contracts or evidence prevents merge.

### 16.2 Per-change evidence

Every implementation PR supplies: affected requirement/test IDs, exact toolchain/source digests, compiled host targets, executed tests, unavailable targets with reasons, actual result counts, before/after performance where relevant, import-closure changes and cleanup evidence. Run independent checks to completion where safe so one early failure does not hide other regressions.

A repair adds a regression test at the earliest practical layer, plus a real-host test when the bug concerns enforcement. Mock tests may accelerate development but cannot replace the designated native-execution gate.

---

## 17. Risk register and decisions not to hide

| Risk | Required mitigation |
|---|---|
| Shared async kernel-plugin not yet available | Static integration slice first; explicit shared-lane dependency; no parallel framework |
| Compiler/interpreter behavior differs across hosts | Native/interpreter parity fixtures; admitted executable baseline; never infer port from syntax check |
| macOS lacks requested generic native container semantics | Explicit native-sandbox/process profile; strict rejection for unavailable guarantees |
| Windows compatibility changes or differs by build | Locked compatibility policy and real allowed/denied tuple tests |
| OCI policy model mistaken for image engine | Separate registry, extraction, snapshot and runtime tasks; native negative tests |
| Network proxy mistaken for isolation | Bypass tests and capability-gated NetworkPolicy |
| Heartbeat timeout mistaken for stopped workload | Fencing/exclusivity policy and partitioned-writer test |
| Provider upgrade loses workload ownership | Versioned recovery records, generation pinning and rollback/drain |
| CI green without execution | Expected test-ID inventory, execution assertions and independent evidence aggregator |
| Privileged test host compromise | Trusted commits, disposable isolated hosts, short credentials and cleanup |
| Lowest-common-denominator API becomes misleading | Common semantics plus explicit requirements, not silent weakening |
| Broad host port delays the usable first slice | Linux vertical slice; Windows/macOS parallel adapters; later FreeBSD/SimpleOS gates |

The project must not promise a single universal isolation implementation. It should promise one API, one explicit capability model, one lifecycle, one observable failure model, and a support matrix justified by execution evidence.

---

## 18. Definition of done and recommended first implementation

The first release candidate is complete only when strict SDN and Simple authoring produce the same canonical resources, real Linux and Windows containers launch without hidden guest-kernel fallback, native macOS workloads participate under their declared class, and the six directed network paths pass with independent evidence. Provider/client restart, image rejection, actual resource enforcement for advertised controls, and complete owned-resource cleanup are required.

Production/HA support remains a separate gate until quorum, recovery, stale-state and fencing scenarios pass. FreeBSD and SimpleOS are not marked supported merely because their adapters compile; their native runtime and new directed network pairs must execute.

**Start with this vertical slice:** strict SDN Pod/Deployment -> sealed resource plan -> one control-plane store -> one node agent -> common container lifecycle -> Linux OCI runtime -> real echo traffic and teardown. In parallel, freeze the Windows process-container and macOS native-workload capability contracts. Extend the same slice to the first cohort before adding broad orchestration features.

**Deliverable status in this review:** repository and documentation inspection, architecture, language/schema proposal, migration plan, native-host policy, parallel work breakdown and CI acceptance design. No repository implementation was changed, no cluster was provisioned, and no native-host or network test was executed.

---

## Appendix A. Repository evidence ledger

All R references use revision `0dc18e8edfc86ea19c81fc6d38fb606d4d0483b1`. R07–R09 are design/research evidence and must not be mistaken for executed acceptance tests.

| ID | File | Inspected area |
|---|---|---|
| R01 | `src/lib/common/sdn/parser.spl` | Lines 1–230: parser APIs, supported shapes, duplicate-key issue behavior |
| R02 | `src/os/services/container/container_manager.spl` | Lines 1–145: MDSOC+/ECS shape, components, Pod state, model spawn |
| R03 | `src/os/services/container/container_runtime.spl` | Lines 1–220: real scheduler launch, hash/root checks, PID binding, exit teardown |
| R04 | `src/os/services/container/oci_import.spl` | Lines 1–190: pure normalized-input edge, no image I/O, textual policy checks |
| R05 | `src/os/services/container/` | Directory inventory, not a storage-execution result |
| R06 | `src/lib/nogc_sync_mut/composition/provider_contract.spl` | Lines 1–170: fixed-width ABI, provider query, digests and handles |
| R07 | `doc/01_research/ui/slim_kernel_plugin/simple_lint_kernel_plugin_mdsocpp_research_design_parallel_plan_2026-09-03.md` | Lines 1–235: predecessor architecture and stated proposed status |
| R08 | `doc/01_research/ui/slim_kernel_plugin/repo_verification_addendum_2026-09-05.md` | Lines 1–180: landed composition versus absent async layer; corroborated directory read |
| R09 | `doc/05_design/runtime/sosix_runtime_unification_design.md` | Initial design/contract/module sections: SOSIX and ring reuse, provider boundaries |
| R10 | `.github/workflows/containerized-tests.yml` | Lines 1–220: Docker/Podman build and discovery invocations |

Pinned repository base for these paths:
`https://github.com/ormastes/simple/blob/0dc18e8edfc86ea19c81fc6d38fb606d4d0483b1/`

The old path referenced in source comments, `doc/04_architecture/os/container/podman_mdsoc_container_arch.md`, returned not-found at this snapshot and was not used as authoritative content. The proposed `src/lib/nogc_async_mut/kernel_plugin/` directory also returned not-found; implementation readiness must be rechecked before starting the dependent tasks.

## Appendix B. External primary-source ledger

Sources were checked during the September 6, 2026 review. Dynamic documentation is not a release lock; actual host/runtime versions must be frozen in the implementation's evidence manifests.

| ID | Source | URL |
|---|---|---|
| E01 | Microsoft: Windows container isolation modes | `https://learn.microsoft.com/en-us/virtualization/windowscontainers/manage-containers/hyperv-container` |
| E02 | Apple: Container project architecture | `https://opensource.apple.com/projects/container/` |
| E03 | Apple: App Sandbox | `https://developer.apple.com/documentation/security/app-sandbox` |
| E04 | FreeBSD Handbook: OCI Containers | `https://docs.freebsd.org/en/books/handbook/containers/` |
| E05 | Microsoft: Windows container version compatibility | `https://learn.microsoft.com/en-us/virtualization/windowscontainers/deploy-containers/version-compatibility` |
| E06 | Kubernetes: Pods | `https://kubernetes.io/docs/concepts/workloads/pods/` |
| E07 | Kubernetes: Windows containers | `https://kubernetes.io/docs/concepts/windows/intro/` |
| E08 | HashiCorp: Nomad architecture | `https://developer.hashicorp.com/nomad/docs/architecture` |
| E09 | HashiCorp: Nomad task-driver authoring | `https://developer.hashicorp.com/nomad/plugins/author/task-driver` |
| E10 | HashiCorp: Nomad jobspec | `https://developer.hashicorp.com/nomad/docs/job-specification` |
| E11 | HashiCorp: Terraform core workflow | `https://developer.hashicorp.com/terraform/intro/core-workflow` |
| E12 | CUE: data validation | `https://cuelang.org/docs/concept/how-cue-enables-data-validation/` |
| E13 | Pkl: language/configuration documentation | `https://pkl-lang.org/main/current/introduction/concepts.html` |
| E14 | Docker: Swarm desired-state services | `https://docs.docker.com/engine/swarm/how-swarm-mode-works/services/` |
| E15 | OCI image index; image configuration | `https://specs.opencontainers.org/image-spec/image-index/` ; `https://specs.opencontainers.org/image-spec/config/` |
| E16 | Podman installation/platform documentation | `https://podman.io/docs/installation` |
| E17 | Microsoft: containerd on Windows | `https://learn.microsoft.com/en-us/virtualization/windowscontainers/deploy-containers/containerd` |
| E18 | HashiCorp: Nomad service discovery | `https://developer.hashicorp.com/nomad/docs/networking/service-discovery` |
| E19 | Microsoft: Host Compute System | `https://learn.microsoft.com/en-us/virtualization/api/hcs/overview` |
| E20 | FreeBSD Handbook: Jails | `https://docs.freebsd.org/en/books/handbook/jails/` |
| E21 | Microsoft: Windows container networking architecture | `https://learn.microsoft.com/en-us/virtualization/windowscontainers/container-networking/architecture` |
| E22 | HashiCorp: Nomad consensus; etcd API guarantees | `https://developer.hashicorp.com/nomad/docs/architecture/cluster/consensus` ; `https://etcd.io/docs/v3.5/learning/api_guarantees/` |
| E23 | GitHub: hosted and self-hosted runners | `https://docs.github.com/en/actions/using-github-hosted-runners/about-github-hosted-runners` ; `https://docs.github.com/en/actions/hosting-your-own-runners/managing-self-hosted-runners/about-self-hosted-runners` |
| E24 | GitHub: secure use reference | `https://docs.github.com/en/actions/reference/security/secure-use` |
| E25 | Tekton: Tasks, Pipelines and concepts | `https://tekton.dev/docs/pipelines/tasks/` ; `https://tekton.dev/docs/pipelines/pipelines/` ; `https://tekton.dev/docs/concepts/overview/` |
| E26 | Microsoft: Windows container security and servicing boundaries | `https://learn.microsoft.com/en-us/virtualization/windowscontainers/manage-containers/container-security` ; `https://www.microsoft.com/en-us/msrc/windows-security-servicing-criteria` |

## Appendix C. Review checklist for every support claim

A reviewer should be able to answer: Which exact artifact ran? On which OS/build and boot instance? Under which effective isolation mode? Which capability was requested, which was enforced, and how was it observed? Did real workload traffic cross hosts? Were negative cases tested? Were cleanup and crash recovery checked? Which tests were not run? Is the claimed support narrower than, equal to, or broader than the evidence?

If these answers are unavailable, retain the implementation work but leave the corresponding support claim open.

---

## Addendum 2026-09-07 — engine default is Podman, and what "native" costs per host

Decided while implementing the CI runner. This addendum records a design change
to §4.2 and §15.3 and two platform facts the original host matrix left implicit.
**Source note:** HTTPS fetching is unavailable in the implementing session
(`native HTTP supports http:// only; HTTPS requires the TLS runtime`), so the
platform claims below are from working knowledge and the measured host probes
quoted, NOT re-verified against E01/E05/E16 this session. Re-verify before
treating them as release evidence.

### Engine preference

The Linux/FreeBSD `native-container` lane prefers **podman**, then **docker**,
then a bare **runc**. Implemented in `probe_container_lane()`
(`src/app/ci/pipeline_runner.spl`). Podman is the default because it is the only
one of the three whose normal mode is rootless, so a CI node need not hand a
daemon root in order to run a build.

### Podman is NOT a native-container engine on Windows

`podman machine` provisions a Linux guest (WSL2 by default, or Hyper-V) and the
engine runs inside it. Podman has no Windows-container backend and does not
drive HCS/`runhcs`, so it cannot produce a process-isolated Windows container.
On Windows, podman is a `virtual-machine`-class engine per §4.1 and the probe
refuses it outright rather than reporting "available with a caveat".

This corrects an asymmetry in §4.2, which named Podman as an option beside
containerd for Windows. The Windows native candidates are **containerd +
runhcs** or **Docker/Moby's Windows-containers backend** — Docker does support
real process-isolated Windows containers in Windows-containers mode, and
separately runs Linux containers in a WSL2 VM.

### Root is not a uniform requirement — it is per host, and it is not the engine

| Host | Native container needs root? | Prerequisites when rootless |
|---|---|---|
| Linux | **No** | user namespaces permitted; `/etc/subuid`+`/etc/subgid` ranges; `newuidmap`/`newgidmap` (`uidmap`); cgroup v2 delegation for enforced limits. Low ports and some network modes still need extra setup. |
| Windows (process isolation) | **Yes — Administrator** | none; there is no rootless Windows container |
| FreeBSD (jail) | **Yes — root** | none; jail creation is privileged |
| macOS | n/a | no native container exists (§4.4) |
| SimpleOS | own policy | decided by the SimpleOS capability model, not by an OCI engine |

Consequence for the contract: engine availability and launch privilege are
**independent** facts and are reported as separate fields (`ProbeV1.engine`,
`ProbeV1.privilege`). An available engine says nothing about the privilege the
launch requires — rootless podman and a root docker daemon both merely
"answered". A receipt must never imply an unprivileged container where none
exists, so `privilege` is `unknown` whenever the lane is unavailable and is
never inferred from the engine name.

### Measured on the implementing host (aarch64 Linux, 2026-09-07)

```
podman ABSENT · docker /usr/bin/docker · runc 1.3.4 · crun ABSENT · newuidmap ABSENT
/etc/subuid: yoon:100000:65536
kernel.apparmor_restrict_unprivileged_userns = 1
```

The lane is BLOCKED, and with podman-first the probe now names the binding
constraint of the next candidate:
`docker-daemon-unreachable: permission denied while trying to connect to the
docker API at unix:///var/run/docker.sock`. Installing podman alone would not
unblock it — `newuidmap` is absent and unprivileged user namespaces are
restricted, so rootless podman would fail where `runc --rootless` already did
(`nsexec: failed to unshare remaining namespaces: Operation not permitted`).
Resume conditions: `doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md`.
