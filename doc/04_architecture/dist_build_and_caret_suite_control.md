# Distributed build and Caret control ownership

Date: 2026-10-12. Branch: `release_phase3`; inspected HEAD: `d5df0cb60`. Status: proposed planning/design, not implemented or runtime-qualified. This lane imports the supplied research without changing its historical claims. Existing uncommitted Caret production artifacts are preserved and remain separately owned. Scope is documentation; requirement selection precedes implementation.

Caret is the authenticated control client. smux/execution owns PTY and process lifecycle; builder manager owns dependency/action identity and parent output admission; common Job admission owns placement and resources; cache gateway owns immutable object quota/pins; protected verifier owns CI trust decisions. Domain contracts remain in their existing common owners. Host syscalls and OS differences remain in SOSIX/provider leaves; app policy is common across OSes.

Chosen proposal: extend these facades with versioned authority/environment bindings and typed SSH broker. Alternative monolithic Caret scheduler reduces initial wiring but duplicates retry/cache authority and is rejected in the source proposal. A mandatory orchestrator/TLS rewrite adds startup dependencies and blocks the SSH slice; retain it as separately gated extension. Apply MDSOC++ to the userland control product; kernel/driver paths remain MDSOC-only.

Startup loads bounded strict configuration and enrolled identities, then opens cached compiled service artifacts. Provider login/build discovery is explicit, not an unconditional startup scan. Request handlers consult indexed grant/session/host records; grant revocation epoch, host generation and environment digest invalidate cached decisions. No repeated full-tree scan or retry sleep belongs in hot handlers. Snapshot capture is explicit, outside terminal-input hot paths.

Performance qualification measures warm startup, representative request p95/p99 and peak RSS under multi-viewer and artifact-transfer fixtures. Numerical release budgets await measured baseline and user selection; absence of those results blocks performance qualification.

See [detail design](../05_design/dist_build_and_caret_suite_control.md) and [plan](../03_plan/app/llm_caret/dist_build_and_caret_suite_control.md).

## MDSOC++ decision and evidence

Definition: MDSOC ownership + optional capsule-local data-oriented state + sealed KPF composition + bounded no-GC asynchronous command/query/event transport + authority, generations, receipts and rollback. See [research definition](../01_research/local/simple_lint_kernel_plugin_library_ide_mdsocpp_research_2026-09-03.md), section 13, and `.claude/agents/spipe/arch.md`. This is a to-be design, not a claim that Caret already composes these capsules.
Current anchors: `src/lib/mdsocpp/model.spl` defines CapsuleDescriptorV1, facet offers/requirements, migrations, seal policy and receipts; `src/lib/mdsocpp/seal.spl` provides composition validation. Reuse common.kernel_plugin identities, contracts and bounded runtime; no second product plugin kernel.

## Layer list and tree encapsulation

| Layer | Actual anchor / proposed addition | Tree-private ownership | Parent / next-layer public surface |
|---|---|---|---|
| L0 host providers | `src/os/apps/smux`, SOSIX host owners | PTY/VT, OS handles, process tree, filesystem enforcement | Existing smux/execution facade; no client access to handles |
| L1 common contracts | `src/lib/common/build_manager`, `src/lib/common/contracts/orchestration`, `src/lib/common/kernel_plugin` | Codecs, validation internals | Immutable versioned build/Job/KPF contracts to L2 and all capsule adapters |
| L2 product composition | `src/lib/mdsocpp/model.spl`, `seal.spl`; proposed `src/app/llm_caret/workbench/distributed_composition.spl` | Registry, routing, bounds, activation journal | Composition admission and generation receipt to L3; no build/session feature state |
| L3 feature capsules | Existing Caret, builder, CI and cache owners; proposed capsule adapters listed below | Each domain owns state, invariants, migration and commands | Required/provided facets carrying values; no sibling-private import |
| L4 clients | Existing cs/workbench/pane paths | Selection, drafts, view revisions | Authenticated commands and read-only queries to L2/L3 facades |

## Common relative tree nodes and visibility matrix

Paths in columns are relative to `src/lib/common`; each populated cell states parent-public (P) and next-layer-public (N). Tree-private remains the default. L3 siblings consume these common nodes directly instead of each other's private code.

| Raw layer | `kernel_plugin/ids` and `contracts` | `build_manager/contracts.spl` | `contracts/orchestration/ci_v1.spl`, `resource_v1.spl` | Proposed `contracts/distributed_control_v2.spl` |
|---|---|---|---|---|
| L0 providers | P: typed status/identity; N: L1 facade only | P: execution values; N: L1 facade only | P: capacity observations; N: L1 facade only | P: no secret handles; N: validated identities only |
| L1 common | P: stable KPF values; N: L2 descriptors | P: immutable action/result; N: L2/L3 contract import | P: Job/resource values; N: L2/L3 contract import | P: grant/operation/environment/evidence envelopes; N: L2/L3 contract import |
| L2 composition | P: generation receipt; N: L3 binding | P: routing envelope; N: L3 build facet | P: resource binding; N: L3 Job facet | P: authorization result; N: L3 immutable request |
| L3 capsules | P: descriptor/facets; N: L4 authorized facade | P: build query/command result; N: L4 values only | P: CI/resource result; N: L4 values only | P: scoped command/query/event; N: L4 bounded value snapshots |
| L4 clients | P: view receipt; N: none | P: view values; N: none | P: view values; N: none | P: user request/view; N: none |

## Capsule graph and required/provided facets

Facet names here are proposed interface identities; seal them to stable KpfId128/version mappings before implementation. Existing owners remain authoritative behind adapters.

| Capsule / proposed adapter | Provides | Requires | Mutable authority | Feature mapping |
|---|---|---|---|---|
| HostAuthority / `src/app/llm_caret/workbench/host_authority_capsule.spl` | HostQueryV2, GrantQueryV2, GrantCommandV2 | host identity/secret-reference provider | enrollment/grants/revocation | F01–03 |
| Session / `src/app/llm_caret/workbench/session_capsule.spl` | SessionCommandV2, SessionQueryV2 | HostQueryV2, execution/smux facade | session bindings and writer/size leases | F04–05 |
| Build / `src/app/bootstrap_builder/distributed_capsule.spl` | BuildCommandV2, BuildQueryV2 | HostQueryV2, ArtifactQueryV2, Job resource facade | DAG, attempts and parent output admission | F06–07,09,14–15 |
| Artifact / `src/app/cache_gateway/distributed_capsule.spl` | ArtifactCommandV2, ArtifactQueryV2 | GrantQueryV2 | reservations, pins and object publication | F08 |
| EvidenceCI / `src/app/ci/distributed_capsule.spl` | EvidenceCommandV2, EvidenceQueryV2 | BuildQueryV2, protected signing/verifier provider | check receipts and CI status | F10,16 |
| SourceLifecycle / proposed builder mirror adapter | SnapshotCommandV2, SnapshotQueryV2 | ArtifactQueryV2, GrantQueryV2 | snapshots/image generations/mirror refs | F11–13 |
| Client / workbench facade | ViewQueryV2 | SessionQueryV2, BuildQueryV2, EvidenceQueryV2 | drafts only | F05,16 |

HostAuthority trust publication and signature verification remain separate from client decoding. The cold reference verifier reads only protected publisher key-policy values and checks distinct issuer/approver signatures bound to the canonical grant and complete operation envelope. A client-supplied public key, authenticated flag, approval boolean or permission mode cannot replace that publisher. Approval-event persistence and the service's non-bypassable admission call remain required. Dynamic message/crypto buffers are outside the admitted no-allocation command path; activation must establish bounded ownership/transfer or a separately declared cold boundary before trusting any critical descriptor. Authored static descriptors are not execution or allocation proof.

Cross-capsule signed values/frames now have a common owner (`distributed_authority_v2.spl` and `distributed_authority_codec_v2.spl`). Clients may encode/decode those untrusted values without importing private HostAuthority keys, its publisher snapshot or verification state. The authority implementation consumes the same metadata validator instead of duplicating protocol shape rules. Public decoding must remain distinct from authenticated authority publication and command admission.

## Sealed composition, lifecycle and ADRs

| Decision | Contract and consequence |
|---|---|
| ADR-DBC-1: compose existing owners | Domain state stays private; adapters publish declared facets, not shared mutable references. No migration of unrelated provider or mobile code is required. |
| ADR-DBC-2: seal before activation | CapsuleDescriptorV1 declares required/provided facets, capability bits, memory/concurrency limits, closure and state migrations. MdsocppSealPolicyV1 binds Userland profile, generation and composition digest; reject missing/ambiguous facets, cycles, denied authority or exceeded budget. |
| ADR-DBC-3: bounded value transport | Commands target one authority; queries do not mutate domain state; events are immutable. Separate bounded event feedback from acyclic static dependency graph; hot intra-owner calls stay direct. Runtime-open providers stay outside static critical proofs. |
| ADR-DBC-4: generations and rollback | Prepare candidate descriptors/migrations, seal, drain old in-flight calls, migrate owned state, atomically activate receipt, then retire old generation after leases settle. Failed activation restores previous generation; irreversible schema changes need explicit restore support. |
| ADR-DBC-5: optional ECS | Initial capsules set uses_ecs=false; later data-oriented optimization stays capsule-local and needs measured benefit. No ECS on kernel/driver/interrupt paths. |

## Migration and rejection gates

| Order | Change | Proof required |
|---|---|---|
| M1a | Extract shared authority/environment/evidence envelopes into common ancestor; keep SessionId and BuildTaskV1 in their existing domain | No duplicate schema or sibling-private import; version compatibility fixtures |
| M1b | Add descriptors/facet identities and seal existing-owner adapter graph | Missing/duplicate/ambiguous facets, cycle, capability/memory/concurrency denial all rejected |
| M2–M4 | Route session/build/cache operations through bounded typed adapters | Lease generation, overload, no mutable cross-capsule references, owner-result admission |
| M5–M7 | Qualify host providers and generation migration/rollback | Native host receipts and crash-at-activation/drain failure fixtures |
| M8 | Add new transport/provider by explicit descriptor generation | Same authorization/action semantics and independent provider qualification |

<!-- sdn-diagram:id=dbc.architecture -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbc.architecture hash=sha256:auto render=ascii
@layout dag
@direction LR
Client -> Composition
Composition -> Session
Composition -> Build
Composition -> EvidenceCI
Session -> HostAuthority
Build -> HostAuthority
Build -> Artifact
EvidenceCI -> Build
Artifact -> CommonContracts
HostAuthority -> CommonContracts
```

</details>
<details class="sdn-ascii" open>
<summary>Diagram — authored preview, generation NOT_RUN</summary>

```ascii generated-from=dbc.architecture hash=sha256:auto
Client -> Composition -> Session -> HostAuthority -> CommonContracts
                      -> Build   -> Artifact      -> CommonContracts
                      -> EvidenceCI -> Build
```

</details>
<!-- sdn-diagram:end -->
