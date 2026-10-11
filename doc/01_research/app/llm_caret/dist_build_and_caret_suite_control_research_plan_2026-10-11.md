# Distributed Build and Caret Suite Control
## Research, repository gap analysis, architecture, and implementation plan

**Date:** 2026-10-11  
**Repository:** `ormastes/simple`  
**Verified `main` snapshot:** `bba9b0989488a37e9b7ab983ae3b2eba640f6229`  
**Status:** proposed integration design, based on read-only source inspection and primary-source research.  
**Delivery:** this document only; no repository modifications, remote sessions, deployments, key creation, or build/test executions were performed.  
**Suggested repository destination:** `doc/01_research/infra/distributed_build/dist_build_and_caret_suite_control_2026-10-11.md`.

## Reading map

| Area | Sections |
|---|---|
| Existing implementation and research | [Repository audit](#2-repository-findings-and-corrections-to-earlier-assessments) · [Research basis](#3-research-basis-and-design-consequences) |
| Caret and SSH control | [Access control](#6-access-control-through-caret-suite) · [Host configuration](#7-host-configuration-roles-addresses-and-keys) · [Remote sessions](#8-remote-llm-sessions-over-ssh) · [UI and tools](#9-caret-user-interface-and-model-facing-tools) |
| Environment-specific execution | [Environment selection](#10-exact-environment-selection) · [Builder integration](#11-distributed-build-execution-and-compiler-efficiency) · [Containers](#12-shs-container-authoring-sdn-deployment-and-pure-simple-migration) |
| Shared infrastructure | [Caches](#13-shared-caches-limits-and-resource-protection) · [Signing and CI](#14-signing-orchestrator-trust-and-github-ci) · [Updates and mirrors](#15-repository-updates-disposable-attempts-and-local-mirrors) · [Transport evolution](#16-transport-evolution-and-the-pure-simple-boundary) |
| Implementation and verification | [Work packages](#17-implementation-plan-and-changes-to-existing-work) · [Acceptance tests](#18-acceptance-failure-injection-and-performance-qualification) · [Definition of done](#19-traceability-operations-and-definition-of-done) · [Sources](#20-source-register) |

## Executive decision

Make **Caret Suite the authenticated user and agent control surface**, not a replacement build scheduler or a container security boundary. A remote LLM session should run on an explicitly authorized host over SSH, retain its native provider interface, and submit build/test/lint requests through the existing distributed builder using an **explicit, immutable execution-environment selection**.

The target flow is:

```text
Human operator in Caret Suite / Simple IDE
   │ authenticates, selects project + remote LLM host, approves scoped access
   ▼
Caret session manager ── SSH ── remote Caret session service
                                  │
                                  ├─ execution service owns process + PTY/ConPTY
                                  ├─ smux owns terminal identity and attachments
                                  └─ user-installed LLM CLI or supported harness
                                              │ narrow build capability
                                              ▼
                                  Shared build submission API
                                              │
                    build dependency/cache owner + common job admission
                                              │
                  exact environment resolution and resource reservation
                                              ▼
                    Linux / Windows / macOS / FreeBSD / SimpleOS worker
                                              │
                   immutable inputs → disposable work → admitted outputs
                                              ▼
                     artifact CAS + signed execution evidence + CI status
```

**The LLM host, build execution host, compilation target, and test execution host are separate choices.** A Codex session on Linux may request a Windows-native build and a Windows-native test; a Windows session may request a Linux build targeting RISC-V. Neither request may silently become a local build or an emulated test.

Use native process-level containers where supported and required. Keep weaker native-process/sandbox and VM/emulation classes explicit. Share immutable cache objects, toolchain images, and qualified read-only compiler indexes; do not share writable attempt directories, credentials, or interactive session state between builds.

SSH is the initial remote-session and compatibility execution transport. Qualified HTTPS/TLS RPC becomes the persistent worker/control transport without changing job semantics. RDMA remains a later, optional artifact/RPC transport. Completing a pure-Simple TLS stack or RDMA provider must not block the first secure SSH-based vertical slice.

---

## 1. Scope and operating model

### 1.1 Required user workflows

**Remote coding session.** The operator chooses a host and project in Caret, launches an installed LLM harness over SSH, sees its terminal in the existing dashboard, detaches, and later reattaches to the same managed session. Session creation, terminal input, file modification, and process termination require distinct permissions.

**Environment-specific build.** The remote LLM invokes a typed build tool with an environment profile and an immutable source snapshot. The builder finds an authorized matching worker, or returns an explicit mismatch/unavailability result. Logs and diagnostics return to the originating Caret session with the actual environment identity.

**Distributed CI.** Local and GitHub-triggered CI use the same job execution and receipt path. A protected verifier may reuse valid authorized evidence; it must not equate a skipped job, a developer signature, or a cached terminal message with independently executed tests.

**Fresh builds without temporary-file management.** Repository changes produce new source snapshots. Each attempt gets a new writable directory/container layer; caches persist under quotas. Restarting a build discards attempt scratch only after execution and artifact ownership are settled. It never discards the LLM's uncommitted edits.

**Local mirror.** A managed Git mirror supplies pinned source objects to the snapshot service. It is separate from the writable agent worktree and from the artifact cache. A mirror update cannot change an already admitted build.

### 1.2 Service profiles

Configure independent roles rather than one mutually exclusive mode:

| Profile | Enabled services | Explicitly absent by default |
|---|---|---|
| Caret client | UI, local authentication, remote connection client | Scheduler, build executor, signer |
| Remote LLM host | Session service, execution service, smux, provider adapters | Build worker, deployment authority, release keys |
| Orchestration-only | Resource API, placement, reconciliation | Compilation, LLM sessions |
| Distributed-build-only | Build manager and/or executor as separately selected | Long-running service deployment controllers |
| CI worker | Approved check execution, artifact upload | General remote login, trust-policy editing |
| Cache/mirror node | CAS gateway and/or source mirror | Build execution unless separately enabled |
| Combined development host | Explicit combination with separate accounts/budgets | Implicit privilege sharing between services |

The common job service is a reusable library/service boundary; running a build-only profile does not require the full service orchestrator.

---

## 2. Repository findings and corrections to earlier assessments

### 2.1 Evidence method

The GitHub `main` ref was read and resolved to the snapshot on the cover. Source reads were pinned to it. Findings below distinguish **inspected implementation**, **repository-reported execution evidence**, **existing design**, and **proposed work**. Search results are not a complete tree audit. An absent result means *not verified here*, not proof that no implementation exists anywhere.

No live branch-protection settings, installed host binaries, credentials, or multi-host tests were inspected. A dated lane report remains evidence reported by the repository, not a test rerun by this audit.

### 2.2 Current foundations

| Area | Evidence observed | What can be reused | Remaining qualification/change |
|---|---|---|---|
| Caret tool permissions | `PermissionPolicy`, `permission_decision`, and real tool executors in `src/app/llm_caret/tools.spl`. Read tools are auto-allowed; mutation uses allow lists/default mode. [R01] | One public permission gate and typed tool entry | Add project/host/session/environment scopes; remote enforcement; bounded delegation; confidential-read policy |
| Caret file/shell boundary | `guard_path` performs textual root/traversal checks; the inspected shell executor invokes `/bin/sh` and a `timeout` command. [R01] | Existing entry points, not their portability/security assumptions | Descriptor-relative no-follow file access; reparse-point handling; explicit execution profile; OS-neutral process owner |
| Caret Suite UI | `cs` requirements define harness/provider/model grammar, agent roster, selection, and native panes. [R02] | Keep `cs`, existing launch grammar, and provider adapters | Add remote host/project/environment selection without overloading provider grammar |
| Windows Caret/smux | October 3 lane state reports ConPTY/smux, pane-backend, Claude/Codex/Kimi, and local-model scenarios passing on a phase-1 Windows seed. It also records stale deployed seeds, missing usage samples, and an unresolved workbench seam. [R03] | Working source-level Windows terminal/provider path | Qualify deployed binary separately; do not repeat the older blanket claim that Windows Caret is unimplemented |
| Builder ownership | Existing architecture assigns immutable contracts to `common/build_manager`, dependency/retry logic to the manager, process/staging to transport, and output admission to the parent. [R04] | These canonical owners | Connect Caret and CI as clients; no second build engine |
| Builder host/task model | `BuildHostV1` contains ID, transport, endpoint, workspace, worker program/digest, and slots. `BuildTaskV1` includes source/producer/toolchain digests and limits. [R05] | Existing V1 contracts and validation | Add versioned environment, principal, policy, run-platform, capability and evidence bindings |
| SSH builder transport | Real source constructs SSH/SCP calls, validates input/worker hashes, creates exclusive attempt roots, and waits for terminal/reap evidence. [R06] | Initial compatibility transport and recovery principles | It uses POSIX paths/utilities and rejects non-local typed links; it is not a proven native Windows SSH transport |
| Capacity controls | Builder architecture reports October 2 native Linux owner integration tests, while rebuilt manager/worker compiler-task qualification remains pending. [R04] | Owned cgroup/JobObject capacity model | End-to-end compiler execution, cross-host overlap, cleanup, and Windows qualification |
| CI/container integration | `pipeline_runner.spl` consumes common orchestration Job contracts and a Linux OCI provider, with explicit blocked outcomes. [R07] | Job expansion and receipts | Cross-host executor integration and actual per-platform runtime proof |
| Signed GitHub evidence | `.github/workflows/pr-fast-check.yml` already retrieves a base-owned script and verifies signed local receipts; it is label-gated and excludes fork jobs. Comments identify unresolved promotion-to-required concerns. [R08] | Existing verifier workflow and receipt transport | Broaden exact check coverage and fix skip/trigger semantics; inspect live rules before claiming required-check coverage |
| Cache limits | `cache_gateway/quota.spl` implements separate main/branch/CAS accounting, TTL policy, and admission outcomes. [R09] | Quota policy and common GC admission | Concurrent reservation correctness, durable accounting, leases/pins, source/toolchain integration, hostile-cache tests |
| Git backup | `push-both.shs` describes guarded GitHub-first push, secondary shallow backup, ref agreement, and optional bundles. [R10] | Backup publication and agreement checks | Managed inbound mirror, ref policy, submodule/LFS handling and recoverable source snapshots |
| Container/orchestrator plan | Existing research defines common SDN contracts, native-provider differences, no silent weaker-isolation fallback, and honest execution evidence. [R11] | Existing requirements and provider architecture | Extend those requirements rather than issue a competing container specification |

### 2.3 Concrete gaps to address first

**G1 — An SSH login is not a Caret authorization decision.** The inspected Caret policy is local and tool-oriented. It does not itself establish a host-scoped delegated identity for a remote session or build worker.

**G2 — A textual path guard is not filesystem confinement.** The current helper does not itself establish symlink/reparse-point-safe resolution. A remotely exposed file API must use the shared host filesystem boundary and actual OS access controls. This is a source-level limitation, not a claim of a completed exploit test. [R01]

**G3 — Existing SSH transport is POSIX-oriented.** It invokes `test`, `sha256sum`, `chmod`, `mkdir`, and `cp`, and uses a slash-prefixed workspace alphabet. A Windows OpenSSH server can use `cmd.exe` or another configured shell; ordinary POSIX quoting cannot be assumed. Replace per-operation shell construction with an installed typed broker, retaining the old path only as an explicitly qualified POSIX compatibility provider. [R06] [E04]

**G4 — Remote source links are not yet portable in the inspected path.** `transport.spl` rejects typed links for non-local transport. The snapshot protocol must carry and validate file/symlink identities rather than silently dereference or discard them. [R06]

**G5 — Environment matching is not represented in the inspected host shape.** A transport endpoint and worker digest are insufficient to prove Windows-native execution, libc/SDK identity, native versus emulated testing, or SIMD settings. [R05]

**G6 — Signed GitHub verification already exists.** The change is integration and policy completion, not writing the first verifier. Repository workflow comments are not live ruleset evidence. [R08]

**G7 — Documentation needs reconciliation.** The `cs` requirements reference `doc/05_design/app/llm_caret/cs_caret_suite.md`; a pinned fetch returned 404. Locate a canonical replacement or restore the missing target and repair traceability. Do not generate another broken link. [R02]

### 2.4 How this updates the previous nine-feature plan

| Previous feature | Decision in this document |
|---|---|
| SHS container descriptors and platform variance | One authoring pipeline into canonical SDN; provider-only variance; explicit script runtime |
| Host SDN and key management | Shared host registry, independent service roles, separate identities and secret references |
| Build/test/lint/orchestrator signing | Common evidence model; different signing authorities; workload cannot access trusted signer |
| GitHub reuse of signed checks | Extend existing base-owned verifier, never raw skip markers |
| Shared bounded caches | Reuse quota/GC; immutable CAS; active pins; isolated mutable attempts |
| Distribute builds to clients | Capability-matched workers and explicit execution profiles, including opportunistic clients |
| CI | Same admission/execution/receipt path as Caret builds |
| Current source and disposable images | Snapshot source separately from toolchain image; drain/replace workers; preserve edits |
| Local GitHub mirror | One-way canonical fetch by default; controlled outbound publication; snapshot/CAS separation |

---

## 3. Research basis and design consequences

The following are reference points, not claims that Simple implements those systems or achieves their performance.

| Reference | Established point | Application to this plan |
|---|---|---|
| **Build systems à la carte**, Mokhov, Mitchell, Peyton Jones, ICFP 2018 | A systematic framework decomposes and compares build-system components. [E01] | Separate dependency/rebuild policy from execution placement and transports; reuse the builder instead of embedding it in Caret |
| Bazel remote execution | Build/test actions can execute remotely and reuse outputs; the ecosystem uses a remote execution/caching API. [E02] | Model immutable actions, environments, artifacts and results. Consider an optional REAPI adapter, not a mandatory gRPC rewrite |
| OpenSSH client/server manuals | Host verification, agent forwarding, forced commands, forwarding restrictions and subsystems are distinct controls. [E03] [E05] | Pin host identity; no default agent forwarding; a forced command alone is not sufficient confinement |
| Windows OpenSSH configuration | Windows shell and server behavior differ; `ChrootDirectory` does not confine ordinary `cmd.exe` sessions. [E04] | Typed remote broker plus Windows process/filesystem isolation; do not use SSH chroot as the Windows security model |
| SLSA 1.2 build requirements and provenance | Provenance identity, protected generation and build isolation are separate concerns. [E06] [E07] | Record who requested, where/how work executed, and what was admitted. Keep platform signing keys out of build steps |
| GitHub Actions security and skip behavior | Untrusted code on persistent self-hosted runners is risky; skipped workflows can leave required checks pending. [E08] [E09] | Dedicated trust-separated workers; an always-reporting protected verifier rather than `[skip ci]` |
| Windows process isolation | Process-isolated containers share the host kernel; Hyper-V isolation uses a guest kernel. Cross-boundary shared memory is not a general Windows-container facility. [E10] | Native Windows container lane is distinct from VM execution; do not assume cross-container shared-memory compiler caches |
| Git mirror documentation | Mirror clones map refs and can be updated from their source. [E11] | Keep an owned bare mirror, immutable snapshots, and worktrees separate; do not blindly mirror-push into the canonical remote |
| RPC-over-RDMA, RFC 8166 | RPC can use RDMA through a transport binding with memory/resource-lifetime requirements. [E12] | Preserve the RPC operation model and add a qualified data path later; do not call RDMA traffic HTTPS |

The performance choice is an engineering hypothesis: **avoiding duplicate compilation and transferring fewer immutable inputs is likely more valuable initially than replacing SSH/TCP with a microsecond transport**. Measure end-to-end builds before enabling a specialized transport.

---

## 4. Non-negotiable requirements

Requirement IDs below are proposed additions, to be connected to existing ORCH/build/Caret requirements rather than replacing them.

| ID | Requirement |
|---|---|
| DBC-001 | Caret controls sessions and presents approvals; the remote service independently enforces authorization |
| DBC-002 | Session host, build execution environment, target platform and test runtime are explicitly separate |
| DBC-003 | Unknown host, changed host identity, missing policy, unsupported isolation, or unmatched exact environment fails closed |
| DBC-004 | Native LLM CLI/provider authentication and permission interfaces remain authoritative; no automatic approval of provider prompts |
| DBC-005 | SSH credentials, node TLS identity, LLM provider credentials, receipt signer and release/deployment signer have separate scopes |
| DBC-006 | Human approval is an authenticated event bound to an immutable request, not an LLM-supplied `confirm: true` |
| DBC-007 | Every job uses a content-identified snapshot, toolchain and effective environment; no mutable branch alias remains at execution |
| DBC-008 | Existing build manager owns compilation dependencies and output admission; common job service owns placement/resource admission |
| DBC-009 | Each execution has owned process-tree identity, attempt root, limits, cancellation and terminal settlement |
| DBC-010 | Only immutable caches are shared across independent jobs; mutable state is attempt- or explicitly qualified group-owned |
| DBC-011 | Native-container requests never silently downgrade to a process, sandbox, WSL or VM |
| DBC-012 | SHS authoring and direct SDN produce the same validated, digest-bound deployment/build plan |
| DBC-013 | GitHub evidence reuse is check-specific, source/environment/policy-bound and enforced by protected verifier code |
| DBC-014 | Repository updates do not mutate active snapshots; retry scratch cleanup does not remove user edits |
| DBC-015 | Node health, capability discovery, compilation and real execution are separately evidenced |
| DBC-016 | Quotas cover local and remote cache bytes, disk reserve, pinned objects, temporary transfers and retention |
| DBC-017 | Session detach, LLM-turn cancellation, job cancellation, session termination and history deletion are distinct operations |
| DBC-018 | Native control/configuration is SDN or bounded binary; required external formats stay at adapters |
| DBC-019 | A compromised build/session cannot obtain an infrastructure signer or broaden its own authorization |
| DBC-020 | Revocation and stale-generation checks apply to existing sessions, new input, submissions and publication |
| DBC-021 | A transport timeout never proves process death or permits blind duplicate execution |
| DBC-022 | Implementations report PASS, FAIL, BLOCKED, UNSUPPORTED, NOT_RUN, CANCELLED and unknown ownership distinctly |
| DBC-023 | Shared ownership and platform variance use existing SOSIX/MDSOC++ conventions without parallel registries |
| DBC-024 | SSH-first delivery remains possible without waiting for pure-Simple TLS, a new orchestrator, or RDMA |

---

## 5. Component ownership and shared contracts

### 5.1 One owner per responsibility

| Component | Owns | Must not own |
|---|---|---|
| Caret/IDE workspace | Selection, views, connection status, approval presentation, task navigation | Trust decisions based only on UI state; direct host syscalls |
| Agent/session manager | Session metadata, provider selection, delegated identity, worktree lease, audit/recovery | Compiler dependency graph or cache publication |
| smux | Terminal identity, screen/input stream, attachment and resize arbitration | A second independent process killer or authorization database |
| Execution service / SOSIX process owner | Actual processes, PTY/ConPTY, resource boundary, child-tree wait/kill/reap | Deployment policy or compiler semantics |
| Common job admission | Authorized placement, budgets, queueing, leases, worker generation | Language-specific invalidation or HIR/MIR cache logic |
| Build manager | Compile DAG, producer/toolchain identity, grouped compile execution, result admission | LLM provider session management |
| Container core + provider | Image/root setup and actual isolation/lifecycle | Independent scheduler, credentials, GitHub policy |
| Cache gateway | Immutable object admission, trust namespaces, quotas, GC, pins | Treating client-declared role as authority |
| Evidence/CI verifier | Signature/policy evaluation and check coverage | Issuing unrestricted execution or release credentials |
| SCV/mirror/snapshot service | Pinned source identities and safe materialization | Mutating active workspaces to follow `main` |

During migration, existing smux or Caret code that currently spawns a process delegates through one execution-owner adapter. Do not introduce a new daemon solely to duplicate an existing owner. A single-process development profile may compose these ports in-process; a remote host uses the same contracts behind an authenticated service.

### 5.2 Versioned contract families

Extend existing contracts compatibly. Proposed records include:

```text
PrincipalRef             user/service identity + issuer + tenant/project
DelegatedSessionV1       human owner + agent identity + scopes + expiry + generation
HostProfileV2            stable ID + roles + endpoints + trust references
EnvironmentProfileV1    execution constraints + target defaults + qualification rules
EnvironmentBindingV1    resolved host/boot/provider/toolchain/image + evidence digests
SessionOpenV1           immutable host/project/harness/model/workspace request
JobSubmitV2             source/action/environment/policy + limits + delegation reference
ExecutionAttemptV2      task/attempt/host/boot/process-tree/lease identities
ArtifactSetV1           relative paths + types + sizes + content digests
ExecutionReceiptV2      observed result + environment + artifacts + provenance links
ApprovalGrantV1         exact request digest + approver + scope + expiry + nonce
```

These are logical schema names, not claims that the repository already exports them. Keep `BuildHostV1` and `BuildTaskV1` readable through explicit version adapters. Older workers must reject unsupported required constraints; they must not ignore a V2 field and run with weaker behavior.

Use the existing SDN parser with strict schema validation. Reject duplicate keys, excessive nesting, unknown mandatory fields, invalid IDs and overlong collections. Resolve symbolic IDs once into typed identifiers; avoid repetitive OS/role/string dispatch in hot loops. Do not introduce a second OS/ISA enumeration beside the platform-variation plan.

---

## 6. Access control through Caret Suite

### 6.1 Identity and authorization chain

The desired chain is:

```text
Authenticated human
  → project role
  → approved remote session
  → short-lived, bounded agent delegation
  → permitted build environment + action
  → worker execution grant
  → evidence admission
```

A node certificate proves a service identity. An SSH credential proves an SSH account identity. Neither automatically grants permission to start an LLM, read a project, build on another host, publish a cache entry, or deploy a service.

Effective permission is the intersection of **organization policy, host policy, project policy, human grant, session scope, action scope, and runtime capability**. A lower-trust source can narrow permission but cannot enlarge it.

### 6.2 Permissions to expose

| Permission | Scope examples | Typical LLM-session default |
|---|---|---|
| `host.discover` | Authorized host/profile metadata | Allow within assigned project |
| `session.open` | Host, project, harness, runtime class | Requires preauthorization or human approval |
| `session.observe` | Session/output channel | Own session only |
| `session.input` | Session + generation + write lease | Own session only; observers cannot type |
| `workspace.read` | Project paths and data classification | Allow only declared workspace |
| `workspace.write` | Dedicated worktree and allowed paths | Grant per session/project |
| `build.submit` | Environment allowlist, named targets, budgets | Bounded grant; no arbitrary worker URL |
| `test.submit` / `lint.submit` | Named suites/rules and runtime class | Bounded grant |
| `job.cancel` | Own task, project operator override | Own jobs only |
| `artifact.read` | Project, namespace and result identity | Own authorized outputs |
| `cache.publish` | Private/untrusted namespace | No direct trusted-main publication |
| `deployment.apply` | Resource plan digest and environment | Deny by default |
| `trust.manage` / `key.enroll` | Administrative trust roots | Human administrative action only |
| `receipt.sign.trusted` / `release.publish` | Platform/release policy | Never granted to LLM or build steps |

Read-only is not synonymous with harmless: private source, terminal logs, credentials and artifacts can be confidential. Replace the blanket read-tool default at remote boundaries with object-scoped authorization. Keep a convenient local development policy only as an explicit profile. [R01]

### 6.3 Approval semantics

An approval record binds the request digest, human principal, project, host/environment, session generation, allowed actions, limits, policy digest and expiration. A model can request approval but cannot manufacture it. A Boolean confirmation field from an MCP/LLM tool is only a request attribute.

Caret displays the *effective* action before approval: destination host, provider, native/container/VM class, repository snapshot, network access, secrets involved, and maximum resource budget. Changing any approval-bound field creates a new request.

A batch grant may authorize repeated builds on a fixed profile with a cumulative budget. It must not authorize new hosts, arbitrary shell commands, broader mounts, secret access, or release publication. New high-risk operations require a separate grant.

### 6.4 Delegation, revocation and enforcement

Use a proven authenticated token/envelope design through the common identity service rather than inventing a cryptosystem. Bind tokens to intended service/audience, human owner, agent identity, session generation, project, action set, host/environment allowlist, expiration and maximum delegation depth. Persist operation IDs for duplicate detection. Proof-of-possession or channel binding is preferable to a freely replayable bearer credential where supported.

The remote session service and job gateway validate independently. A token is not accepted merely because it arrived over SSH. Local IPC permissions bind the requesting process to its session; a sibling process must not steal an unrestricted build capability from a shared file or environment.

Revocation increments a policy/session epoch. Stop new terminal input and job admission immediately once observed; disconnect unauthorized attachments. Define whether in-flight jobs drain or terminate by policy, and separately revoke permission to publish. During partitions, refuse renewal and new privileged work; running bounded work may finish within an already admitted lease, but its output still needs current admission policy.

### 6.5 OS isolation is mandatory for hostile workloads

Caret tool gating cannot confine arbitrary code after a shell/toolchain process is permitted. Enforce filesystem/network/process boundaries through the runtime provider. The broker runs outside the user workload with only the privileges needed for its lifecycle API; never mount its control socket or signer secrets into the workload.

For untrusted forks or unknown LLM-generated scripts, use a separately qualified high-isolation worker class or dedicated machine. Do not promise that process containers alone provide the same protection as a hardware boundary. Trusted personal development may use native process-level isolation for efficiency, with the weaker trust class recorded. [E08] [E10]

---

## 7. Host configuration, roles, addresses and keys

### 7.1 Configuration ownership

Keep machine environment/toolchain configuration separate from trust policy but link both through one host registry. Proposed separation:

```text
project/config/build/             build targets and environment requests
project/config/container/         common recipe and permitted variants
project/config/deploy/            declarative SDN resources
host-owned config/host/           local paths, service roles, endpoints, capacities
host-owned trust policy          principals, grants, public trust roots, revocation
credential store                 private keys and provider secrets; not in Git
```

Project files may request capabilities; they cannot enable a server role, enroll a signer, change SSH host trust, disable isolation, or install a credential provider. Effective merged configuration records source origin and a digest. An LLM-editable checkout never overrides host-owned trust.

### 7.2 Proposed host SDN example

**Schema illustration only.** The versioned loader and CLI switches below must be implemented and tested; these are not drop-in commands for the current repository. IDs are resolved against typed registries. Example addresses use reserved documentation domains.

```sdn
schema: simple.host-control/v1
host:
  id: win-builder-01
  roles: [build_executor, ci_executor]
  projects: [simple]
  endpoints:
    ssh:
      alias: simple-win-builder-01
      address: builder01.example.invalid
      port: 22
      account: simplebroker
      host_trust_ref: trust.ssh.builder01
      client_identity_ref: credential.ssh.caret_user
    control:
      mode: outbound
      server: https://control.example.invalid:7443
      identity_ref: credential.node.builder01
      trust_ref: trust.cluster.development
  execution:
    allowed_profiles: [windows_x64_msvc_native]
    default_profile: windows_x64_msvc_native
    max_parallel_jobs: 4
    memory_reserve_bytes: 8589934592
    allow_llm_sessions: false
    allow_deployments: false
  storage:
    workspace_root_ref: path.builder.work
    cache_root_ref: path.builder.cache
    cache_max_bytes: 107374182400
    disk_reserve_bytes: 21474836480
```

A second host can declare `roles: [caret_session_host]` and no build execution. A coordinator can declare `roles: [orchestrator, build_coordinator]` without executor slots. Role grants are independent from technical capability discovery: detecting an installed compiler does not authorize building on that machine.

### 7.3 Credential lifecycle

Keep these separate even when using the same public-key algorithm:

| Credential | Purpose | Must not be available to |
|---|---|---|
| SSH user key/certificate | Open approved remote broker/session connection | Remote LLM files, images, build containers |
| SSH host key/host CA | Authenticate remote host | Client-controlled enrollment logic |
| Node TLS identity | Worker/control service authentication | User build steps |
| LLM provider credential | Provider inference/authentication for a session | Other users/sessions; compiler containers |
| Developer receipt key | Explicit developer assertion | Unapproved autonomous agent processes |
| Trusted execution signer | Platform-generated evidence | LLM, compiler, test script, SSH shell |
| Deployment/release signer | Approve exact artifacts/resources | Ordinary worker/service identity |

Use OS-protected credential providers and restrictive ACLs. Never place private key bytes in SDN, images, Git, terminal replay, command arguments or CAS. Log only public key IDs/fingerprints and authorization decisions.

Use pinned SSH host keys or a managed host CA; first enrollment and changed identity require a human-controlled trust path. Do not equate `ssh-keyscan` output with authenticated enrollment. `ForwardAgent` defaults to off. For bastions use a verified jump-host route without lending the remote host an unrestricted local agent. OpenSSH documents that a forwarded agent can be used for authentication by a sufficiently privileged remote attacker even when key bytes are not extractable. [E03] [E13]

Support expiry, rotation and revocation per credential class. Rotating an SSH login key must not silently rotate an artifact publisher or trust a different node TLS key. A host identifier is stable; hostname/IP is mutable connection metadata.

---

## 8. Remote LLM sessions over SSH

### 8.1 Two deliberately different modes

**Managed session mode — preferred.** SSH connects to a fixed installed Caret broker/subsystem. A bounded structured request opens or attaches to a persistent remote session. The remote execution owner creates the real PTY/ConPTY and provider process. Closing the SSH connection detaches the view, not the process.

**Direct interactive compatibility mode.** A human can open an explicitly allowed native SSH terminal and launch a provider. This is a broader remote-shell capability, not the restricted build API. Persistence requires a qualified remote multiplexer/session service; a plain SSH login alone does not provide Caret recovery semantics.

Do not represent the compatibility mode as fully managed when ownership or reconnect cannot be proven. Do not auto-fallback from managed mode to unrestricted remote shell.

### 8.2 Session-opening protocol

1. Resolve a configured host ID and project. Load host-owned policy; verify the SSH host identity and installed broker identity against the admission profile.
2. Authenticate the human/service connection. Resolve the caller through a trusted identity source, not a claimed username in the request.
3. Negotiate a bounded protocol version and capability set. Report installed provider executable/version/digest, PTY/ConPTY capability, runtime classes and workspace roots. Discovery is not successful launch evidence.
4. Authorize the immutable `SessionOpenV1`, including provider/harness, workspace, network/credential policy and resource budget.
5. Acquire an exclusive worktree/session lease. Materialize the selected repository generation without modifying another session's tree.
6. Launch through the remote execution owner using structured executable/argv/environment, and record session ID, generation, host boot ID, process-tree identity and terminal identity.
7. Attach the Caret view to normalized session events and terminal bytes. Record last acknowledged sequence for reconnect.
8. Delegate only the permitted build/test/lint capability to this session. The LLM receives tool endpoints and permitted environment IDs, not raw infrastructure keys.

The SSH subsystem transport itself should normally be **non-PTY** so its framed binary/SDN messages are not altered by terminal processing. The broker separately allocates the provider PTY/ConPTY. Interactive direct-SSH mode may request an SSH PTY, but that is a separate transport mode.

### 8.3 Avoid a remote-shell injection boundary

Use one fixed broker entry point and send dynamic fields in a bounded message over standard input or a registered subsystem. Do not construct:

```text
ssh host "cd <LLM path> && <LLM command> ..."
```

Even correct local argv handling does not turn the remote SSH command field into an argv-preserving protocol. The existing builder's POSIX shell construction should remain isolated in a compatibility adapter while the typed broker replaces it. [R06]

Where `ForceCommand` is used, its command is administrator-owned and never interpolates `SSH_ORIGINAL_COMMAND`. Disable unwanted forwarding separately: OpenSSH explicitly notes that a forced command alone does not disable TCP, agent or X11 forwarding. A subsystem/restricted-command configuration still needs OS confinement. [E05]

On Windows, validate the installed OpenSSH service, configured shell behavior, broker path and ConPTY integration. Do not change the machine's default SSH shell simply to make POSIX scripts work. A native broker handles path normalization, process creation, timeouts and file hashes through SOSIX/Windows providers. `ChrootDirectory` must not be treated as confinement for a normal Windows command shell. [E04]

### 8.4 Provider adapters and credentials

Preserve the existing `harness[:provider][/model]` concept; host selection is a separate field. Do not append `@host` or shell fragments to the provider string. A remote capability probe determines which provider adapter is actually available. [R02]

Use the user's installed Claude/Codex/Gemini/Kimi or other supported executable; do not bundle provider binaries or infer that every provider accepts another provider's flags. Native CLI mode keeps its TUI and native approvals visible. Structured mode uses a documented, capability-probed provider API only where supported. This plan does not claim any particular current CLI flag set or commercial entitlement.

Credentials are resolved on the authorized remote host through the session credential provider or the provider's supported native login flow. Human login/MFA remains human-controlled. Do not copy a local provider home directory or forward the workstation's general SSH agent to make login convenient. Browser callbacks, where necessary, require an explicit scoped tunnel and must not create a public unauthenticated listener.

For SimpleOS or another host unable to run a vendor CLI, keep the LLM process on a supported host and use the remote execution/build interface for the project target. A remote project environment need not be able to run the LLM provider itself.

### 8.5 Session state and concurrency

```text
requested → authorized → provisioning → running ↔ detached
                                      ├→ draining → exited
                                      ├→ failed
                                      └→ ownership_unknown → reconciled
```

Persist session generation, host boot ID, provider process identity, worktree lease, delegation epoch and event sequence. `detached` is an attachment state; the provider may still be running. `ownership_unknown` is not an exit state.

Allow many read-only viewers, but one active terminal-input lease unless explicit collaboration is enabled. Lease transfer is an authenticated event. Preview panes do not resize the remote PTY; only the active size owner does. Capture the destination session ID and generation when the user submits input; changing UI selection while a request is queued must not retarget it.

Keep separate operations for detach, stop current provider turn, cancel a build, terminate the entire session, and delete retained history. A process exit or SSH disconnect must not be used as permission to kill unrelated jobs. Session termination may cancel its own jobs only according to the recorded ownership policy.

### 8.6 Terminal safety

Terminal output is untrusted data. Bound scrollback, event size and replay retention. Do not execute generated shell links, clipboard escape sequences, file-transfer escapes, or approval-looking text automatically. Display provider output as provider output, not as trusted Caret UI chrome.

Passwords and tokens must not be recorded through keylogging of login flows. Capture raw terminal history only under an explicit privacy policy; structured audit can record operation IDs and decisions without preserving secret keystrokes. Redaction is defense in depth, not permission to expose secrets to an untrusted process.

---

## 9. Caret user interface and model-facing tools

### 9.1 Extend the existing workbench

Keep the current left-side agent/status area and main terminal view. Add a host/project/environment inspector and an approval queue, rather than a new independent dashboard.

The active session header should distinguish:

```text
Session: A7 · generation 12 · Codex · SSH connected
LLM host: dev-linux-01 · workspace: simple/A7 · trust: personal
Build profile: windows_x64_msvc_native · actual worker: win-builder-01
Source snapshot: sha256:… · target: windows/x86_64/msvc
Test mode: native · isolation: windows-process-container
```

Before a build is admitted, actual worker fields show `not assigned`; an unavailable usage measurement shows `unknown`, not zero. A discovered profile is visibly different from a recently qualified environment. Repository lane reports already emphasize not fabricating unavailable usage data. [R02] [R03]

Approvals show a semantic diff from the session's existing grant: new host, more memory, different runtime class, external network, write mount, or deployment. Reconnection displays whether the same process survived or a new generation was created.

### 9.2 Proposed CLI extensions

**New interface proposal, not currently implemented command syntax.** Preserve current `cs` launch commands and add structured remote/build namespaces:

```text
cs remote hosts --project simple --format sdn
cs remote open --host dev-linux-01 --project simple --harness codex
cs remote attach --session A7
cs remote detach --session A7
cs remote terminate --session A7

simple build environments --project simple --format sdn
simple build plan --target compiler --exec-env windows_x64_msvc_native --format sdn
simple build submit --plan PLAN_ID --snapshot SNAPSHOT_ID --format sdn
simple build watch --run RUN_ID --format sdn
simple test submit --artifact ARTIFACT_SET --run-env windows_x64_native --format sdn
```

`plan` resolves constraints and reports eligibility/required approval without execution. `submit` accepts an immutable plan reference, not a command assembled by the LLM. A changed snapshot or environment invalidates the plan binding as specified by policy.

### 9.3 Typed tools for LLM use

| Tool | Input | Result |
|---|---|---|
| `build.environments` | Project + authorized filter | Permitted profiles and observed qualification state |
| `workspace.snapshot` | Own worktree + selected input policy | Frozen snapshot ID; dirty-source provenance |
| `build.plan` | Named target + snapshot + execution/target constraints | Plan digest, matched profiles, denial reasons, approval request |
| `build.submit` | Admitted plan ID + operation ID | Run ID and captured environment binding |
| `build.status` / `build.logs` | Run ID + event cursor | Structured status, diagnostics and bounded logs |
| `test.submit` / `lint.submit` | Artifact/source identity + approved suite/rules | Run ID with independent runtime/rules binding |
| `job.cancel` | Own run ID + reason | Cancellation request state, not fabricated terminal success |
| `artifact.get` | Admitted artifact ID + destination capability | Verified materialization receipt |

The tool service resolves the session principal itself. A model cannot select `signer`, `trusted: true`, an arbitrary hostname, a host path outside its workspace, or a raw executable to bypass target policy. Approved compiler targets may execute code, so they still run under the selected workload boundary.

Native tool requests/results are SDN or binary. MCP, provider JSON, OCI JSON and GitHub YAML are **edge formats** where required by external protocols. Convert at one adapter; do not fork validation or introduce JSON as the internal configuration authority.

---

## 10. Exact environment selection

### 10.1 Four identities, not one label

| Identity | Meaning | Example |
|---|---|---|
| Session environment | Where the LLM/harness and interactive workspace run | Linux development host |
| Execution environment | Where the compiler/build action runs | Windows process container with MSVC SDK |
| Target platform | ABI/ISA/runtime generated by compilation | RISC-V 64-bit bare metal, RVV disabled |
| Test environment | Where the resulting executable is exercised | Physical RISC-V board, QEMU, or a native Windows host |

A successful cross-compile proves neither native execution nor hardware compatibility. An emulated test must be labeled emulated. A Windows-target build produced on Linux must not satisfy a requirement to build *on Windows*. These distinctions are part of the requested result contract.

### 10.2 Environment profile versus observed binding

An **environment profile** is an immutable desired recipe: OS family/build constraints, architecture, ABI, libc or SDK, toolchain/image digests, compiler backend, target feature mask, driver/runtime requirements, and isolation class.

An **environment binding** is the admitted execution: host ID/boot ID, current provider generation, resolved image/toolchain digests, effective resource limits, probes, test execution mode, policy digest and timestamp. User-friendly aliases resolve to these immutable identities before scheduling.

Example profile proposal:

```sdn
schema: simple.build-environment/v1
id: windows_x64_msvc_native
execution:
  os: windows
  arch: x86_64
  abi: msvc
  mode: native
  runtime_class: native_container
  provider: windows_process
  host_image_compatibility: required
  toolchain_ref: toolchain.simple_qualified_msvc
  sdk_ref: sdk.windows_qualified
  image_ref: image.windows_builder_qualified
target_defaults:
  os: windows
  arch: x86_64
  abi: msvc
selection:
  matching: exact_required_fields
  weaker_isolation_fallback: false
  emulation_fallback: false
  local_fallback: false
qualification:
  require_worker_roundtrip: true
  require_compiler_execution: true
  require_process_tree_cleanup: true
```

All referenced versions/digests must resolve through a committed environment lock or host-owned approved registry. The example intentionally does not invent current SDK/compiler version support.

### 10.3 Platform-variation integration

Reuse one platform resolver for OS, ABI, pointer width, CPU/ISA, SIMD, GPU backend and runtime provider. Container and build selection must not maintain another independent OS string table.

Distinguish **host features available** from **target code-generation features enabled**. Disabling AVX-512 or RVV in a target profile means the compiler must not emit those instructions; it does not require a host CPU physically lacking them. Conversely, native tests of code that uses a feature require runtime capability evidence. Keep x86 baseline/AVX/AVX-512, ARM64, RV32/RV64 and RVV controls explicit, including a baseline RV64IMAC profile where applicable.

MinGW and MSVC are different Windows ABI/toolchain profiles. WSL2 is a Linux environment on a Windows machine, not Windows-native execution. macOS builds requiring Apple tooling need a qualified macOS execution host; placing Linux in a VM does not supply that native environment.

### 10.4 Selection algorithm

Filter authorized hosts first, then apply required environment predicates. Check requested runtime class, native/emulated mode, locked toolchain/image, ISA/backend capabilities and current qualification. Reserve memory/CPU/disk against actual host headroom. Rank only the remaining matches using cache locality, queue delay, transfer size and configured fairness.

Revalidate host boot/provider generation and immutable image/toolchain identity immediately before spawn. Return structured reasons such as `ENV_NO_MATCH`, `ENV_NATIVE_REQUIRED`, `ENV_TOOLCHAIN_MISMATCH`, `ENV_NOT_QUALIFIED`, or `CAPACITY_UNAVAILABLE`; do not silently substitute a convenient local host.

Cache compatibility and execution placement are related but not identical. Store the effective environment in evidence; include every output-relevant environment property in the action key. Do not include transient IP addresses or host IDs unless the action genuinely depends on them. A hardware-specific test result has a stricter reuse policy than a deterministic architecture-independent source analysis.

---

## 11. Distributed build execution and compiler efficiency

### 11.1 Reuse the existing builder

The builder keeps its compile DAG, exact producer/input identities, retry rules and parent-owned output admission. Caret submits work through this owner; CI submits the same kind of work. Common job admission adds authorized placement and capacity without becoming a second compiler scheduler. [R04] [R05]

Preserve the planned process hierarchy:

```text
Build manager
  ├─ node job broker
  │    ├─ grouped compiler process / middle manager
  │    │    ├─ compiler worker thread or isolated child
  │    │    └─ compiler worker thread or isolated child
  │    └─ another admitted group
  └─ another node job broker
```

Inside one qualified group, share immutable frontend/index data and explicitly synchronized or single-owner internal state. Across trust boundaries or independent attempts, share only immutable encoded artifacts. Do not transmit object pointers, mutable compiler heaps, lock state or arena addresses to another host.

Make compiler caches and builder caches cooperate through the existing common cache/identity interface. Reuse parse/HIR/MIR or TLDR data only with exact schema, source, producer, backend and relevant variation identities. A syntax-only artifact may have a wider compatibility domain than an ABI-specific object; encode that distinction rather than hashing the whole host indiscriminately.

### 11.2 Snapshot construction

The LLM edits a session-owned worktree. A snapshot service freezes declared inputs, file modes, symlink identities, submodule content, generated inputs and toolchain references. It must detect edits during copying/hashing and either retry under a read barrier or emit a verified immutable snapshot. A timestamp or Git branch name alone is insufficient.

Dirty work is allowed in a **development trust namespace**. Record its base commit and full snapshot digest; do not describe it as CI on an exact committed tree. Authoritative CI/release uses the admitted committed or explicitly merge-generated source tree required by policy.

Do not send `.ssh`, provider homes, ignored credential files, arbitrary parent directories, or ambient environment variables. Input policy defines what can be exported to a remote host, including source classification and project data restrictions.

### 11.3 Action identity

Proposed canonical action key:

```text
H(
  action_schema_version,
  source_manifest_and_transitive_inputs,
  toolchain_and_producer_digests,
  executable_argv_and_declared_environment,
  effective_target_and_output_relevant_execution_profile,
  generated_inputs_and_plugin_digests,
  declared_output_contract
)
```

Keep retry attempt IDs and ephemeral worker addresses out of reusable action identity; keep them in execution identity. Network-fetched dependencies must be materialized and locked before execution or the action must be explicitly marked non-hermetic/non-reusable under the relevant policy.

A digest proves the bytes match the named content. It does not prove that the compiler used those bytes correctly or that an untrusted worker actually ran the declared command. High-trust promotion requires an authorized execution producer and, where selected, independent rebuild/test comparison.

### 11.4 Job lifecycle

```text
planned → authorized → queued → leased → materializing → running
                                                       │
                        failed/cancelled/unknown ←──────┤
                                                       ▼
                           exited → collecting → validating → admitted
                                                                      │
                                                           cleanup → settled
```

Process exit, artifact admission, cleanup and final settlement are separate facts. CI can expose a validated build result while cleanup is pending, but must not label the whole execution clean or admit a replacement using the same owned boundary prematurely. A cleanup failure remains visible and blocks unsafe resource reuse.

For the first implementation, preserve the existing conservative retry rule: do not retry an attempt whose owned process tree is not proven reaped. Later, pure hermetic compilation can support speculative execution using fresh isolated attempts and fenced single publication, but that is a separate feature and cannot be generalized to deployment, flashing or arbitrary scripts. [R04] [R06]

### 11.5 Artifact transfer and client delivery

Use manifest-based missing-blob negotiation, resumable bounded uploads and digest verification. Transfer source blobs once per cache miss, not one SSH/SCP operation per source file. Compress where measured useful; never base64 binary artifacts inside terminal or SDN text.

Workers write to attempt-owned staging. The parent validates the declared output set, relative paths, types, sizes, task/attempt/environment identity and digests before immutable publication. The requesting client materializes admitted outputs through the same no-follow filesystem service; a returned artifact cannot overwrite arbitrary workspace/host paths.

Large logs and test traces are artifact objects with access-controlled references. Stream summaries and structured diagnostics separately. Link diagnostics to the exact source snapshot so an LLM does not apply an old error location to a newly edited file without noticing.

### 11.6 Personal/client workers

A client may offer capacity without becoming an orchestrator or an LLM host. Require explicit opt-in, project allowlist, CPU/memory reserve, concurrency and disk budgets, idle/battery policy where available, and a drain switch. An untrusted personal worker's receipt remains lower trust; requesting a nominal environment must not grant it trusted-main cache or release authority.

---

## 12. SHS container authoring, SDN deployment and pure-Simple migration

### 12.1 One canonical plan

Use this pipeline:

```text
SHS authoring script OR direct SDN
  → existing parser / script engine
  → typed common recipe + allowed platform overlay
  → strict validation + dependency lock
  → immutable SDN/binary plan and digest
  → authorization/signing
  → host runtime provider
```

The authoring script runs under a bounded authoring policy, not as arbitrary code inside the privileged orchestrator. Only the validated output plan is admitted. It captures every artifact, base-image digest, build step, effective variable and provider-specific field needed for reproduction.

A `.shs` suffix alone does not establish a portable native Simple script: the inspected mirror script is explicitly `#!/bin/sh`, and the current shell tool also invokes `/bin/sh`. Preserve working compatibility scripts while adding an explicit runtime/grammar identity. Do not relabel POSIX shell as pure Simple. [R01] [R10]

Define a script API around structured operations—copy an input, run an approved executable/argv, declare outputs, select an environment, publish a plan. Exact SHS syntax must follow the existing `sosh`/SHS grammar. This document does not invent executable grammar for an unverified parser.

### 12.2 Platform overlays

Common recipe fields include process argv, source/toolchain identities, read-only root, writable scratch, limits, network policy and output declarations. Provider overlays contain only unavoidable OS differences:

| Provider | Provider-specific responsibility | Not an acceptable substitute |
|---|---|---|
| Linux native container | Namespaces, cgroups, filesystem mounts, privilege/seccomp policy | Ordinary process with only a memory cap |
| Windows process container | HCS-backed isolation, compatible host/image, Windows filesystem/network rules | JobObject alone; WSL; Hyper-V while claiming native-process isolation |
| FreeBSD jail | Jail identity, filesystem/network/resource controls | Generic POSIX process |
| macOS native process/sandbox | Explicitly qualified native execution restrictions | Claiming Linux-equivalent container isolation |
| SimpleOS container | Actual kernel capability/process/filesystem enforcement | Container-manager state model alone |

Process-level execution avoids a per-workload guest kernel where the host supports that isolation class; it does not guarantee zero overhead. Image materialization, filesystem layers, network policy, quotas and security hooks still need measurement. Windows documents the distinction between process and Hyper-V isolation. [E10]

### 12.3 What “pure Simple” means

Implement shared authoring, validation, policy, lifecycle and orchestration logic in Simple. Replace external runtime command adapters incrementally with Simple provider implementations **without duplicating shared policy**.

Hosted providers still call native host interfaces through SOSIX/SFFI/syscalls. Windows HCS and host kernel services are not eliminated by writing the calling code in Simple. A Linux-native Simple runtime can eventually replace selected `runc`/`crun` functions, but only after equivalent isolation, cleanup and interoperability tests. Pure-Simple protocol/crypto implementations require their own verification; implementation language is not a security or conformance certificate.

### 12.4 Environment shape for efficient builds

Keep the LLM session outside the disposable build container. Use a digest-pinned toolchain/base image plus an immutable source snapshot and fresh scratch. Avoid rebuilding the entire base image on every source edit. A single run may group related compile tasks inside one qualified boundary to amortize startup while retaining task identities and output isolation.

Do not mount host SSH/provider/signing directories, an unrestricted container-daemon socket, or a writable trusted cache inside the build. Where Windows containers cannot share a host memory object across isolation boundaries, use immutable file/CAS materialization or an authenticated broker; keep shared-memory optimization within a compatible boundary. [E10]

---

## 13. Shared caches, limits and resource protection

### 13.1 Cache hierarchy

```text
compiler/group-local memory cache
  → per-host immutable artifact/parse cache
  → authorized shared cache gateway
  → backing CAS storage
```

Keep one logical cache authority and client API, with separate physical policies for parse metadata, objects, toolchains, source snapshots and image layers. Use existing quota/GC logic rather than adding another ad hoc eviction loop. The current gateway has main/branch/CAS budget and TTL structures; it is a foundation, not by itself proof of concurrent durable storage correctness. [R09]

### 13.2 Required cache behavior

| Concern | Required behavior |
|---|---|
| Lookup | Local first; bounded remote lookup; one in-flight fetch per authorized digest |
| Integrity | Verify digest/type/size before admission and materialization; quarantine corrupt content |
| Authorization | Namespace/project checks on read and write; a content hash is not an access capability |
| Publication | Worker submits candidate; trusted gateway admits according to producer/evidence policy |
| Mutable state | Separate per-attempt work/cache namespace; no cross-job writable mount |
| Retention | Protect main/release and active references; expire stale branch/user data under policy |
| Pinning | Active leases pin inputs/toolchains and unsettled outputs; crashes require lease recovery |
| Quota | Reserve before concurrent upload; commit accounting atomically; roll back abandoned reservations |
| Disk pressure | Preserve a free-space reserve and bound temporary downloads/log spools as well as final objects |
| Failure | Cache unavailable/full is a miss or skipped publication, not fabricated build failure; missing required source/output storage remains a real blocker |

Main/release priority is not unlimited retention. Keep project/branch budgets and global physical-disk bounds. Shared blobs referenced by several namespaces require correct reference/accounting policy; deleting one branch must not delete a still-pinned main object.

A gateway quota call must be serialized or paired with an atomic reservation ledger; multiple callers cannot all pass admission against the same unreserved free bytes. Reconcile ledger and storage after a crash before admitting more writes. This is an implementation acceptance requirement, not an assertion that the current complete gateway is racy.

### 13.3 Performance and ownership

Read-only memory-mapped indexes can be shared where the platform and isolation boundary support them. Changes create new versions, not in-place mutation. Small trusted local jobs may use an in-process cache client; remote jobs use the same contracts through a gateway. Batching and event notifications should replace frequent full-directory scans.

Never let an LLM's ability to run a compiler imply permission to write a trusted action-result mapping. Cache poisoning can produce a byte-valid but semantically false result if provenance and action binding are absent. Use trust-separated namespaces and current admission policy in addition to hashing. [E06]

---

## 14. Signing, orchestrator trust and GitHub CI

### 14.1 Four separate signed statements

| Statement | What it establishes | Producer |
|---|---|---|
| Request/approval grant | This principal may execute this exact bounded action | Authorization service / authenticated human grant |
| Execution receipt | This execution service reports this task/result/environment | Node or execution evidence service |
| Verification/admission receipt | These artifacts/check results satisfy this versioned policy | Protected verifier |
| Deployment/release authorization | These exact image/artifact/resource digests may be published/applied | Separately authorized deployment/release service |

Signing the orchestrator binary/plugin and signing a deployment plan are different operations. Startup admission validates the broker/controller executable and plugin digests against a trusted release policy. Runtime authorization validates the requested resource/action. A trusted binary does not authorize every request; a signed request does not prove the host ran an untampered binary.

A developer receipt remains a developer assertion. Trusted-platform receipts require a generator outside the user-defined build/LLM environment, backed by observable execution facts. A signature proves origin/integrity under a key; it is not proof of correct execution by an untrusted worker. SLSA distinguishes these properties and requires protection of provenance secrets from build steps for stronger guarantees. [E06] [E07]

### 14.2 Evidence contents

Use one common versioned envelope with a typed payload for build, test, lint, image, deployment and admission. Bind:

```text
schema and signature domain
requester / agent / execution producer identities
source snapshot and committed-tree or dirty-work classification
action plan, target, toolchain, image and effective environment
host boot / provider / task / attempt identities
check manifest, rule/test selection and relevant policy digests
exit and verdict, declared outputs, logs/evidence digests
start/end observations, freshness, nonce and supersession references
```

Sign canonical bytes with explicit schema/version/domain separation. Keep the existing receipt wire/signature format stable during migration; do not canonicalize old signed text differently and expect its old signature to remain valid. Provide explicit old-format verification adapters and a separately versioned new envelope.

Signing keys reside in a protected service/keystore; the API signs only evidence it can validate and is authorized to produce. Do not expose a general “sign arbitrary bytes” endpoint to agents. Do not sign each terminal byte or heartbeat: authenticated channels protect routine messages; durable grants, final evidence and publication decisions receive signatures.

### 14.3 Existing GitHub workflow: extend, do not replace blindly

The inspected `pr-fast-check.yml` already uses base-owned verification logic, a read-only token, no persisted checkout credentials, and receipts on `refs/notes/pr-fast-receipts`. Its actual trigger is a label event with `ci:full`; fork jobs are excluded. Its comments say it is not yet a required check and list coverage/budget/skip concerns. This is source evidence only, not live GitHub ruleset inspection. [R08]

Required changes:

- Preserve a protected, always-reporting verification job for every applicable PR head and merge-queue revision. Receipt reuse skips covered *work*, not the final required check.
- Compare the exact tree/ref under test, check manifest, environment/toolchain where relevant, trusted signer policy and expiration/revocation. Rebase-stable work identity is supplementary; changed input bytes require revalidation.
- Define outcomes separately: accepted equivalent evidence; no/invalid evidence with safe full-check fallback; unsupported/unavailable checks; unauthorized request. Never convert a failed or blocked required test into success.
- A no-source-change PR needs policy-defined applicability, not an empty evidence set accidentally counted as a pass. A fork cannot satisfy required work simply because its job was skipped.
- Check current rulesets and merge-queue configuration before rollout. Do not infer enforcement from YAML comments.

Do not use `[skip ci]` or commit-message skip instructions as the mechanism. GitHub documents that skipped workflows can leave required checks pending. A `pull_request_target` verifier must not execute PR-controlled source/scripts/actions with privileged access. The existing base-owned pattern needs end-to-end qualification and SHA-pinned action dependencies. [E08] [E09]

### 14.4 CI trust tiers

| Work | Execution pool | Receipt reuse / publication policy |
|---|---|---|
| Personal dirty development | Authorized personal worker | Private development cache; no claim of committed CI |
| Trusted branch CI | Isolated project worker | Branch-scoped reuse after policy validation |
| Untrusted fork | Dedicated/strongly isolated untrusted pool, no infrastructure secrets | No trusted-main write or release authority |
| Main/release CI | Qualified protected execution pool | Trusted admission, retention and promotion policy |
| Hardware-specific tests | Explicit physical target or explicitly labeled emulator | Reuse only under a matching test/evidence policy |

Build, test, lint, traceability, convention, duplication and review checks retain separate manifests/results. A build PASS is not a test PASS; an LLM review is not a compiler/linter execution receipt. Preserve the project's required SPipe/model-review gates, but keep their authority and evidence types distinct.

---

## 15. Repository updates, disposable attempts and local mirrors

### 15.1 Update source, not an active build

Use this sequence:

```text
local edit or approved remote ref update
  → mirror/worktree source event
  → freeze a new snapshot
  → create a new build plan/run identity
  → reuse compatible immutable cache objects
  → execute in fresh scratch
  → validate and publish outputs
  → settle and clean old attempt resources
```

Source changes normally require a new snapshot, not a new toolchain image. Rebuild a base/toolchain image when its recipe or locked dependencies change. A worker deployment tracks an immutable image generation; a branch alias such as `main` resolves to a commit before any build is admitted.

If a new source change arrives during a build, mark the old result as belonging to the old snapshot. Optional latest-only policy cancels queued obsolete work and may request cancellation of active disposable work. It never changes inputs underneath a compiler or reuses the same output directory for the new generation.

### 15.2 Worker/image replacement

For build workers prefer **stop new admission → drain or explicitly cancel owned attempts → validate/upload outputs → settle → replace image → health/qualification probe → resume**. Pin active old images until their references are gone. Rollback selects an already verified older digest, not an arbitrary mutable tag.

Interactive LLM sessions are not disposable build attempts. Do not restart them automatically when a toolchain image changes. Their edits, provider session state, workspace leases and approved credentials have separate lifetime policies. A human session restart can preserve the workspace while recreating the process; it must not erase uncommitted work.

### 15.3 State classification

| State | Lifetime and owner |
|---|---|
| LLM worktree and uncommitted edits | Session/project; preserve until explicit reconciliation/deletion |
| Source snapshot | Immutable CAS object; pin for run and evidence retention |
| Toolchain/base image | Immutable generation; reference-counted retention |
| Compiler attempt scratch | Disposable only after owned execution is settled |
| Shared cache | Persistent, quota-limited, immutable publication |
| Logs and receipts | Retain according to audit/debug policy, independently of scratch |
| Provider credentials | Credential store; never part of snapshot/image/cache |
| Persistent application volume | Explicit application owner; not removed by builder cleanup |

### 15.4 Managed Git mirror

Reuse the existing guarded dual-push backup but do not mistake it for a full-history inbound mirror. The inspected script explicitly describes a shallow backup and GitHub-first authority. [R10]

Add a host-owned mirror service with these boundaries:

**Inbound synchronization:** allowlisted canonical repository URL and refs; authenticated fetch; no automatic execution of fetched hooks/config; serialized ref updates; retain last-known-good refs and report staleness. A repository URL from an LLM cannot become an unrestricted network fetch target.

**Snapshot materialization:** exact commit/tree and submodule gitlinks; explicit URL mapping for intranet mirrors; locked LFS/generated dependencies when used; safe archive/path handling. Preserve upstream submodule identity even when a local mirror supplies the bytes.

**Outbound publication:** separate approval/credential, expected-old-ref checks and protected push/review route. Do not use a blanket mirror push that deletes remote refs or overwrites unrelated work. Maintain signed-receipt notes under a controlled separate ref policy.

**Offline behavior:** allow an explicit pinned available revision; display that it is not freshly verified against upstream. Never claim “latest” when fetch failed. Git mirror refs/history, source snapshots and artifact CAS remain three distinct stores with connected identities. [E11]
---

## 16. Transport evolution and the pure-Simple boundary

### 16.1 One operation contract, several transports

Do not require an HTTPS server, a complete service orchestrator, or a new SSH implementation before delivering the first remote workflow. The existing SSH builder is a useful compatibility route, although its current POSIX assumptions need explicit replacement. [R06]

| Path | Initial role | Contract and qualification boundary |
|---|---|---|
| In-process call | Combined development host | Same authorization/admission semantics; no privileged bypass for local calls |
| Local Unix socket / Windows named pipe | Caret to local execution or submission service | Peer identity, restrictive endpoint permissions, bounded messages and process ownership |
| SSH broker/subsystem | Remote session open/attach and first distributed-build slice | Fixed remote entry, verified host identity, typed request, bounded channel flow control |
| HTTPS/TLS RPC | Later persistent worker registration/control and CAS access | Qualified TLS provider, authenticated peers, scoped requests, reconnect and backpressure |
| Shared-memory ring | Optional qualified same-host acceleration | Explicit ownership and ACLs; no assumption that containers can share arbitrary mappings |
| RDMA | Later opt-in controlled-fabric RPC/bulk transfer | Actual registered memory, provider completion, isolation and independent data-channel security |

Define `submit`, `observe`, `cancel`, `drain`, `fetch_output`, and event-sequence behavior above the transport. A backend must advertise whether it supports streaming, cancellation acknowledgement, resumable transfer or local zero-copy. Unsupported capabilities are rejected or handled by an explicit contract-preserving adapter, not silently emulated with weaker semantics.

Keep terminal streams and artifact traffic on separate bounded channels/queues. A large CAS upload must not consume every connection credit needed for cancellation, approval, heartbeat or terminal interaction. Apply both per-session and host-wide memory limits to receive buffers and queued events.

### 16.2 HTTPS and TLS qualification

The previous discussion identified several TLS/HTTPS implementation paths; this document does **not** re-audit their current cryptographic completeness. Before selecting a default provider, qualify real client/server interoperability, certificate and hostname verification, client identity, record fragmentation, malformed inputs, cancellation, connection limits and key rotation. A source file named TLS is not sufficient evidence for Internet exposure.

Reuse a shared secure-stream abstraction rather than another TLS stack inside Caret or the builder. Hosted mature providers can coexist with a pure-Simple provider behind the same boundary. Promote the pure-Simple provider only after equivalent acceptance and independent security review; keep the choice visible in deployment evidence. The first SSH-based slice does not depend on that promotion.

Worker-initiated persistent control connections suit hosts without inbound service exposure. A restricted SSH tunnel can be an explicitly configured compatibility path. Do not open unauthenticated public listeners, disable identity checking, or let an LLM choose arbitrary tunnel destinations. Transport authentication establishes a peer; application authorization still decides which project, environment and operation that peer may use.

### 16.3 RDMA later, without changing authorization

RPC-over-RDMA is a real standardized transport family, but RFC 8166 concerns ONC RPC: it does not make the current Simple protocol or gRPC automatically RDMA-compatible. Use it as a reference for a separately specified optional transport. [E12]

Begin with two-sided messaging and completion integration; add registered bulk buffers only after lifecycle correctness. Bind every registration to a principal, job/attempt generation, protection domain, permitted operation, length and lifetime. Never accept a remote process pointer as authorization. Treat remote-access keys as sensitive capabilities, not public object IDs.

A cancellation or disconnected connection does not prove that a device has stopped referencing a buffer. Retirement requires the provider-specific completion/drain/invalidation procedure before reuse. Reconnection negotiates fresh authority; it must not resurrect stale memory grants. Benchmark real hardware, not modeled queue-pair or completion records.

An authenticated HTTPS negotiation channel does not encrypt RDMA data. Require a separately qualified data-protection policy appropriate to the deployment, or refuse the backend. Preserve TCP/SSH/TLS fallbacks at the operation boundary, with the same attempt identity and duplicate-execution rules. RDMA is an optimization project, not a prerequisite for distributed compilation.

### 16.4 What “pure Simple” means here

The goal is Simple ownership of schemas, policy, scheduling, receipts, session logic, RPC framing, cache coordination and runtime management. Host kernel interfaces, Windows HCS/ConPTY, device drivers, and user-installed commercial LLM CLIs remain external dependencies where appropriate.

Replacing an external runtime or transport adapter is a separate provider qualification. It must not duplicate common algorithms or delay a secure functional implementation. A `.shs` filename does not certify its interpreter: the inspected mirror script explicitly uses `/bin/sh`. Record the authoring language, interpreter identity and digest in each executable build step. [R10]

---

## 17. Implementation plan and changes to existing work

### 17.1 Delivery sequence

Implement a vertical slice first, then widen platforms and trust classes. The milestones below are proposed work packages, not claims that the corresponding feature is already delivered.

| Milestone | Work and existing owner | Depends on | Exit evidence |
|---|---|---|---|
| M0 — Reproducible baseline | Inventory actual Caret, smux, builder, CI and runtime binaries; record source/digest/provider versions; repair broken traceability links | None | Baseline SDN ledger distinguishes source inspection, reported tests and freshly executed tests |
| M1 — Scoped host/session contracts | Extend existing common contracts with principal, grant, session, environment, operation and evidence identities; strict SDN validation | M0 | Negative authorization/schema tests pass; V1/V2 compatibility policy executable |
| M2 — Managed SSH session | Connect `cs` and its existing manager/pane path to a fixed remote broker; execution service owns PTY/process, smux owns attachment | M1 | Real remote LLM launch, human approval, detach/reattach and wrong-host rejection on an admitted Linux host |
| M3 — Exact remote build | Add environment resolution and Caret build tools to the existing builder; typed remote staging replaces POSIX-only assumptions | M1; M2 for integrated UI | The remote LLM requests one allowed environment; actual worker, target and outputs match the immutable request |
| M4 — Shared CAS and grouped execution | Connect existing compiler/cache owners to authenticated snapshots, single-flight fetch, quotas, pins and parent-only publication | M3 | Repeat builds reuse admitted objects; concurrent jobs cannot corrupt shared state or exceed reservations |
| M5 — Native Windows qualification | Native SSH broker, ConPTY, environment probe, structured process execution, filesystem/reparse handling; separate container lane | M2–M4 | Linux→Windows and Windows→Linux session/build paths with actual environment receipts; process mode never labeled container mode |
| M6 — Signed CI convergence | Connect Pipeline Jobs and trusted execution evidence; extend existing base-owned GitHub verification rather than add a bypass | M3–M5 | Exact-source and exact-environment evidence accepted; altered, stale and insufficient-trust evidence rejected |
| M7 — Container, image and mirror lifecycle | Qualify native providers; SHS/SDN authoring; immutable source/image generations; guarded mirror controller | M3–M6; native provider prerequisites | Rebuild/restart/rollback preserve active ownership, caches and uncommitted session work |
| M8 — Other hosts and transport optimization | macOS explicit runtime classes, FreeBSD, SimpleOS, ARM/RISC-V; qualified TLS provider, then optional RDMA | Relevant earlier contracts | Per-profile native/emulated/cross-compiled evidence; transport parity and measured benefit |

M2–M4 may start with an explicitly trusted `native-process` worker. They must not advertise container confinement or run hostile multi-tenant work. An unavailable native-container provider blocks that isolation lane, not every low-privilege personal development workflow.

The first end-to-end scenario is: **Caret on host A → managed SSH LLM session on host B → typed build request for an exact environment on host C → validated artifacts and diagnostics back to the originating session**. A, B and C may initially be two physical hosts with distinct services; tests must state the topology. A same-process mock is not a cross-host result.

### 17.2 Concrete modification map

New paths below are proposed locations within existing ownership domains, not assertions that those files already exist. Preserve public facades while migrating; reconcile exact directory placement with the existing SOSIX/variation plan before moving code.

| Existing anchor | Change | Keep out of this owner |
|---|---|---|
| `src/app/llm_caret/tools.spl` [R01] | Make policy decisions consume an immutable caller/grant context; add typed build adapters; replace lexical-only file authority with shared safe filesystem operations | Scheduler, private key storage, independent container implementation |
| Existing `cs` manager and pane backend [R02] [R03] | Remote host/session selection, connection state, input lease, explicit approvals, actual build-environment display | Separate process supervisor or duplicated terminal emulator |
| `src/lib/common/build_manager/contracts.spl` [R05] | Versioned environment and authority bindings; compatibility decoder with rejection of unsupported required fields | Host syscalls, UI state, provider-specific shell syntax |
| `src/app/bootstrap_builder/transport.spl` [R06] | Keep legacy SSH in a compatibility adapter; add fixed-broker structured execution and snapshot transfer | Reimplementation of DAG/cache semantics |
| Builder manager/worker ownership [R04] | Resolve exact environment before reservation; enforce capabilities again on worker; retain attempt settlement and parent admission | Provider-CLI controls or interactive approval prompts |
| `src/app/ci/pipeline_runner.spl` [R07] | Submit shared Jobs through local/remote executor; structured logs/evidence and genuine platform boot identities | Another compile scheduler or “skip means pass” conversion |
| `src/app/cache_gateway/` quota owner [R09] | Authorized lookup/upload, atomic quota reservations, pins, namespace-specific promotion, recovery | Writable workspace synchronization |
| `.github/workflows/pr-fast-check.yml` and existing receipt scripts [R08] | Preserve protected-base verification; widen event/coverage handling under explicit trust policy; report required checks consistently | Execution of untrusted PR code in the trusted verification context |
| `scripts/scv-migration/push-both.shs` [R10] | Retain guarded outbound backup; add separately owned inbound mirror/snapshot controller | Unrestricted bidirectional `--mirror` operations |
| Container contracts/providers [R07] [R11] | Shared resolved descriptor, explicit platform runtime class, provider evidence and image generations | Caret-specific identities embedded into host kernel APIs |

Add shared contract modules only where an existing canonical owner cannot represent the concept. In particular, `ExecutionGrant`, `EnvironmentBinding`, `SessionIdentity` and evidence envelopes need one owner each, not parallel Caret/build/CI definitions. Domain-specific data remains in its domain: the build manager owns compile keys and dependency graphs; the session manager owns interactive sessions.

### 17.3 Update existing plans instead of accumulating conflicting plans

The existing Caret requirements should gain remote-session and delegated-build requirements, while retaining the launch grammar and honesty constraints. Reconcile the older Windows pane wording with the later smux/ConPTY evidence, and repair the referenced design link that returned 404 at the inspected snapshot. [R02] [R03]

The builder architecture should add explicit environment resolution, remote structured execution and scoped principals without weakening its current no-duplicate-retry or parent-admission rules. Preserve the distinction between successful native capacity probes and a fully qualified compiled-worker run. [R04] [R05] [R06]

The container/orchestrator plan should consume the same execution grant and environment binding. It must not become a dependency of every build-only installation. Preserve its typed runtime classes and no-weaker-fallback rule. [R11]

The signed-receipt plan must record that a real workflow is already wired. Remaining work is policy/coverage/qualification, not simply “implement a verifier.” Repository comments about required checks are not a replacement for reading the live ruleset during rollout. [R08]

### 17.4 Parallel work without integration drift

After M1 freezes the initial wire contracts, session transport, environment/worker integration, and cache/evidence integration can proceed in separate worktrees. Assign one owner to each shared schema, CLI namespace and configuration resolver. Each change includes negative tests and a compatibility fixture before adapters consume it.

Separate directory moves from behavioral changes. Keep an old transport/provider selectable only when its capability report is honest. Do not silently read a V2 request with a V1 decoder, silently drop an environment constraint, or route a failed managed session through an unrestricted shell. Retire compatibility paths only after their users and failure cases have migrated.

---

## 18. Acceptance, failure injection and performance qualification

### 18.1 Evidence levels

Every test receipt states whether it is a schema/model test, local native test, cross-host test, or hardware-provider test. It includes source revision, executable/runtime digests, actual host identity, environment binding, isolation class, fixtures, start/end observations and cleanup outcome. A source check, discovered test name, or simulated completion cannot be promoted into native execution evidence.

The scenarios below are proposed acceptance tests. They were not executed while preparing this document.

| Test | Scenario | Required result |
|---|---|---|
| AT-01 | SSH host key differs from the enrolled identity | Refuse session; no automatic acceptance or credential forwarding |
| AT-02 | Session-open request includes shell metacharacters, newlines or oversized fields | Bounded typed validation; dynamic input never becomes remote shell source |
| AT-03 | LLM supplies `confirm: true`, a forged approval ID, or an approval for different bytes | No authority gained; only matching trusted approval/grant is accepted |
| AT-04 | Session requests another project's files, cache objects, logs or workers | Denied even for otherwise read-only operations |
| AT-05 | Authorized build tool attempts privileged deployment, signer access or unrestricted SSH | Denied; operation scopes remain separate |
| AT-06 | Workspace contains symlinks, Windows reparse points, alternate path spellings or case collisions | Safe filesystem policy enforced at use; no lexical-only escape or TOCTOU authorization |
| AT-07 | Provider executable is absent, changed, or lacks the requested adapter capability | Structured error; no fake terminal or invented provider output |
| AT-08 | Detach and reconnect during a real provider turn | Same surviving session/process identity is restored, or actual loss is reported |
| AT-09 | UI selection changes while terminal input is queued | Input remains bound to the captured session/generation; stale lease rejected |
| AT-10 | Two viewers try to control one terminal or resize through preview panes | Input/size lease ownership enforced; passive previews do not resize it |
| AT-11 | Grant revoked or expires while a worker is disconnected | Admission/renewal follow bounded offline policy; stale grant cannot authorize a new operation or publication |
| AT-12 | LLM asks for Windows-native execution but only Linux/cross-compilation is available | Explicit unsatisfied environment; no local or emulated fallback |
| AT-13 | Compiler, SDK, ABI, enabled ISA, optimization mode or declared environment changes | Relevant action/environment digest changes; incompatible result cache rejected |
| AT-14 | Hardware is discovered but native test actually runs under emulation | Receipt records emulation; native requirement is unsatisfied |
| AT-15 | LLM edits files while source snapshot is being captured | Stable snapshot or detected/retried capture; no mixed revision admitted |
| AT-16 | Two compiler attempts mutate scratch and request the same cache object | Scratch isolated; immutable object fetch deduplicated without writable sharing |
| AT-17 | Cache object is corrupted, cross-project, or has valid bytes but unauthorized result provenance | Integrity and authorization checked separately; bad object/result quarantined or ignored |
| AT-18 | Concurrent cache admissions fill disk while active objects are pinned | Atomic limits/reserves honored; no active input eviction; optional cache failure does not corrupt builds |
| AT-19 | SSH connection drops but the remote compiler continues | Ownership becomes uncertain; do not blindly rerun or delete its scratch |
| AT-20 | Process termination/reap or capacity release fails | Terminal cleanup failure remains visible; no clean settlement receipt or premature resource reuse |
| AT-21 | Receipt has wrong source, test selection, policy, environment, artifact digest, signer or expiry | Reject evidence reuse; run an allowed fallback check or report a real failure |
| AT-22 | PR head/base changes, merge candidate changes, or a fork lacks usable trusted evidence | Old success not reused for new bytes; appropriate verifier/fallback reports the actual status |
| AT-23 | Image or mirror updates during active build/session | Active source/image stays pinned; session edits survive; new work selects a new generation |
| AT-24 | Mirror fetch fails, diverges, or submodule mapping supplies wrong content | Explicit stale/conflict result; exact gitlink/snapshot validation; no “latest” claim |
| AT-25 | Secrets appear in environment, provider login, crash paths or audit collection | Secret material excluded from snapshots, cache and routine logs; sensitive recording path disabled or explicitly protected |
| AT-26 | Direct provider CLI bypasses Caret's typed tools and runs its own shell | OS/account sandbox contains the process; UI policy is not credited as process confinement |
| AT-27 | Native Windows container requested where only WSL2/Hyper-V or JobObject process mode works | Correct runtime class or rejection; no native-container claim from mere process limits |
| AT-28 | RDMA buffer grant revoked while work requests remain outstanding | Provider-specific retirement completes before memory reuse; stale generation never reused |

AT-01–11 and AT-25–26 gate remote-session authorization. AT-12–20 gate environment-specific distributed execution. AT-21–24 and AT-27 gate CI/update/native-container claims. AT-28 is required only when RDMA is enabled.

Add sabotage fixtures for the most important checks: deliberately alter an expected environment digest, redirect a workspace link, replay an old generation, and forge an output receipt. A positive-only suite cannot establish that these boundaries reject incorrect behavior.

### 18.2 Platform matrix

Qualify the **client**, **session host**, **build execution host**, **compile target**, and **test execution host** independently. Record native process, native container, sandbox and VM/emulation in separate dimensions. Start with Linux x86-64 and Windows x86-64, then extend only after each host's binary and provider path is available.

An ARM or RISC-V cross-compilation result is valid evidence for output generation, not a native runtime test. A QEMU run is useful but must retain its emulator/version/profile identity. A Windows test through Git Bash does not by itself qualify native Windows process creation or process-isolated containers. MacOS support must retain its distinct sandbox/VM boundary rather than inheriting Linux's capabilities by name.

For each admitted environment, include at least one successful build, one known compiler/test failure, cancellation, disconnect/recovery, resource exhaustion, clean settlement and verified output retrieval. Run shell/path fixtures with spaces and non-ASCII filenames where the profile claims to support them.

### 18.3 Performance plan

Measure end-to-end work before specializing transport. Preserve a native-process baseline and compare a native-container run with identical inputs, compiler, CPU limits and cache state. Any overhead percentage must identify its denominator and exclude neither image setup nor transfer without saying so.

| Measurement | Conditions to keep distinct |
|---|---|
| Session startup and reconnect latency | Cold/warm broker, provider process startup, authentication, surviving vs recreated session |
| Caret input/render responsiveness | Idle, provider streaming, simultaneous large artifact transfer, many passive viewers |
| Build wall time | Local/remote, cold/warm compiler, cold/warm CAS, source/image already present or transferred |
| CPU and memory | Coordinator, session service, provider process, grouped compiler workers, cache service; peak and steady state |
| Cache performance | Hit/miss rate by tier, bytes transferred/avoided, single-flight savings, GC pauses, temporary reservations |
| Queueing and utilization | Authorized eligible workers, resource reservation, task granularity, locality and contention |
| Recovery | Detection, reconnection, ownership reconciliation, safe retry and cleanup measured separately |
| Transport optimization | Same payload/security policy, concurrency and loss conditions; latency distribution and CPU cost |

Report p50/p95/p99 where sample counts justify them, and publish the raw measurements/fixture configuration. Set numerical release budgets from the baseline rather than inventing a speedup. Optimizations must not achieve better throughput by weakening isolation, skipping input validation, dropping logs silently, or pretending unsupported tests passed.

---

## 19. Traceability, operations and definition of done

### 19.1 Documentation and SPipe integration

Keep this file as the research/integration decision record. Add or amend the repository's requirement, architecture, detailed design, implementation plan, Modern SSpec, operator-guide and evidence-report entries under their existing conventions. Map DBC requirements to acceptance scenarios, code owners and observed test receipts; do not duplicate all contracts in every document.

Update the Caret, builder, container/orchestrator, cache and verification SPipe guidance to teach the same workflow: inspect capabilities, choose an exact environment, capture source, request a narrow grant, submit a Job, inspect structured evidence, then retrieve outputs. Repository instructions and remote command output are untrusted content, not permission to widen a grant.

Generated spec mirrors and link checking should run through existing tooling. Fix the broken Caret design reference before treating its requirement chain as complete. The current source snapshot is an audit anchor; implementation work must state its own branch/commit and rerun the affected baseline after rebasing.

### 19.2 Operator controls

Caret should expose inspectable host enrollment, installed-binary qualification, session grants, approval history, active attempts, quota/pin usage and signer identity. It should offer explicit drain, revoke, reconnect, cancel and rollback operations with a preview of their scope.

Missing hosts, unavailable Windows usage measurements, blocked container privileges, unqualified TLS providers and absent signers are actionable states. Do not hide them behind a general “healthy” cluster badge. Read-only inspection must still obey project confidentiality.

First deployment requires an operator to enroll hosts and choose credential providers and runtime classes. This document does not authorize installing privileged services, altering host security policy, joining Docker groups, exposing new network ports, or enrolling signing keys automatically.

### 19.3 Definition of done for the first supported release

The first release is complete only when all of the following are demonstrated on declared supported hosts:

1. Caret opens a real authorized remote LLM session over verified SSH and reattaches without inventing session state or duplicating the provider process.
2. The LLM submits typed build/test/lint requests under a scoped capability; host, project, environment and resource constraints are enforced remotely as well as in the UI.
3. Requested build execution, compilation target and test execution identities match the actual receipt; mismatches fail visibly instead of changing the request.
4. The existing builder executes immutable inputs in isolated attempt storage, admits only validated outputs, and safely reconciles disconnections before retry or deletion.
5. Shared caches honor confidentiality, quotas, pins and publication authority; disposable scratch can be restarted without losing interactive edits or signing material.
6. Signed evidence and CI reuse distinguish developer assertions from trusted execution; the protected GitHub verifier covers the exact tested source/environment and does not bypass required checks.
7. Native-container claims have real provider evidence. Unsupported platforms and transport optimizations remain explicitly unqualified rather than weakening the default.

The complete pure-Simple transport/runtime migration and hardware RDMA support are separately gated extensions. They do not change this release's authorization, environment or evidence contracts.

---

## 20. Source register

### 20.1 Repository evidence

Repository links below are pinned to `bba9b0989488a37e9b7ab983ae3b2eba640f6229`. A source file establishes inspected behavior/structure; a lane or architecture report establishes what the repository reports. Neither substitutes for execution in this audit. Read ranges are stated to avoid implying whole-repository or whole-file coverage where only a relevant section was read.

| Reference | Inspected source and scope |
|---|---|
| [R01] | Caret permission policy, file guard and shell execution; source lines 1–410 |
| [R02] | Caret Suite requirements and launch grammar; complete document; linked detailed-design path returned 404 at this snapshot |
| [R03] | Windows Caret/smux hardening lane; complete report, including reported October 3 tests and deployment caveats |
| [R04] | Bootstrap distributed builder architecture; complete document, including capacity and qualification distinctions |
| [R05] | Common build-manager contracts; source lines 1–235 |
| [R06] | Builder local/SSH transport and immutable staging; source lines 1–250 |
| [R07] | CI pipeline runner, runtime references and host probes; source lines 1–150 |
| [R08] | GitHub PR Fast Check workflow; complete workflow |
| [R09] | Cache gateway quota/TTL/admission implementation; complete file, lines 1–136 |
| [R10] | Guarded GitHub/secondary-backup script; header and setup, lines 1–60 |
| [R11] | Existing orchestrator/container research; lines 1–110, including scope and acceptance requirements |

### 20.2 Papers and primary external references

External references were checked during preparation on 2026-10-11. The research synthesis uses the official publication page for the ICFP paper and the cited specifications/documentation; it does not claim a new benchmark or a complete formal audit of those systems. Upstream documentation is not proof that an installed host version supports every option.

| Reference | Source | Use in this plan |
|---|---|---|
| [E01] | Mokhov, Mitchell and Peyton Jones, **Build Systems à la Carte**, ICFP 2018; official Microsoft Research publication page | Build-system decomposition; preserve separate dependency/rebuild/execution responsibilities |
| [E02] | Bazel, **Remote Execution Overview** | Remote execution/caching as an architectural reference, not a claim of Simple REAPI compatibility |
| [E03] | OpenBSD/OpenSSH, **ssh_config(5)** | Host verification, SSH client policy and forwarding controls |
| [E04] | Microsoft, **OpenSSH Server configuration for Windows** | Native Windows SSH behavior and configuration boundaries |
| [E05] | OpenBSD/OpenSSH, **sshd_config(5)** | Fixed-command/subsystem entry and independent forwarding restrictions |
| [E06] | SLSA v1.2, **Build requirements** | Separate signed claims from trusted build-service isolation and provenance assurance |
| [E07] | SLSA v1.2, **Build provenance** | Provenance fields and external interoperability boundary |
| [E08] | GitHub, **Secure use reference** | Trusted workflow code, limited credentials, untrusted execution separation |
| [E09] | GitHub, **Skipping workflow runs** | Why signed evidence reuse should not be implemented as a workflow-skip bypass |
| [E10] | Microsoft, **Isolation modes** | Windows process isolation versus Hyper-V isolation |
| [E11] | Git, **git-clone documentation** | Bare/mirror repository semantics; distinguish mirror storage from active worktrees |
| [E12] | RFC Editor, **RFC 8166: Remote Direct Memory Access Transport for Remote Procedure Call, Version One** | Concrete RPC-over-RDMA reference; ONC RPC scope, not automatic compatibility |
| [E13] | OpenSSH, **Agent restriction** | Risks and limits of delegated/forwarded SSH-agent use |

[R01]: https://github.com/ormastes/simple/blob/bba9b0989488a37e9b7ab983ae3b2eba640f6229/src/app/llm_caret/tools.spl
[R02]: https://github.com/ormastes/simple/blob/bba9b0989488a37e9b7ab983ae3b2eba640f6229/doc/02_requirements/feature/cs_caret_suite.md
[R03]: https://github.com/ormastes/simple/blob/bba9b0989488a37e9b7ab983ae3b2eba640f6229/.spipe/caret_suite_harden/state.md
[R04]: https://github.com/ormastes/simple/blob/bba9b0989488a37e9b7ab983ae3b2eba640f6229/doc/04_architecture/bootstrap_distributed_builder.md
[R05]: https://github.com/ormastes/simple/blob/bba9b0989488a37e9b7ab983ae3b2eba640f6229/src/lib/common/build_manager/contracts.spl
[R06]: https://github.com/ormastes/simple/blob/bba9b0989488a37e9b7ab983ae3b2eba640f6229/src/app/bootstrap_builder/transport.spl
[R07]: https://github.com/ormastes/simple/blob/bba9b0989488a37e9b7ab983ae3b2eba640f6229/src/app/ci/pipeline_runner.spl
[R08]: https://github.com/ormastes/simple/blob/bba9b0989488a37e9b7ab983ae3b2eba640f6229/.github/workflows/pr-fast-check.yml
[R09]: https://github.com/ormastes/simple/blob/bba9b0989488a37e9b7ab983ae3b2eba640f6229/src/app/cache_gateway/quota.spl
[R10]: https://github.com/ormastes/simple/blob/bba9b0989488a37e9b7ab983ae3b2eba640f6229/scripts/scv-migration/push-both.shs
[R11]: https://github.com/ormastes/simple/blob/bba9b0989488a37e9b7ab983ae3b2eba640f6229/doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md
[E01]: https://www.microsoft.com/en-us/research/publication/build-systems-la-carte/
[E02]: https://bazel.build/remote/rbe
[E03]: https://man.openbsd.org/ssh_config
[E04]: https://learn.microsoft.com/en-us/windows-server/administration/openssh/openssh-server-configuration
[E05]: https://man.openbsd.org/sshd_config
[E06]: https://slsa.dev/spec/v1.2/build-requirements
[E07]: https://slsa.dev/spec/v1.2/build-provenance
[E08]: https://docs.github.com/en/actions/reference/security/secure-use
[E09]: https://docs.github.com/en/actions/how-tos/manage-workflow-runs/skip-workflow-runs
[E10]: https://learn.microsoft.com/en-us/virtualization/windowscontainers/manage-containers/hyperv-container
[E11]: https://git-scm.com/docs/git-clone
[E12]: https://www.rfc-editor.org/info/rfc8166/
[E13]: https://www.openssh.org/agent-restrict.html
