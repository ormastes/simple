# Kernel Plugin Fabric Agent Tasks

**Status:** Proposed
**Merge owner:** KPF integration owner (highest-capability model)
**Final reviewer:** Independent architecture/verification owner, not an implementation-lane author

## Coordination Contract

- Agents execute in isolated workspaces and commit locally; no shared-worktree edits.
- V1 schema and generated artifacts have one exclusive owner.
- Cross-owned changes are handoff requests, not opportunistic edits.
- Every lane records decisions, paths, commands, measurements, blockers, and commit in `.spipe/kernel-plugin-fabric/<lane>/state.md`.
- Integration reruns each authoritative acceptance command once; agent-reported green is not sufficient.
- No lane may weaken a fail-closed result, coverage predicate, capacity, or test.
- Lower-model sidecars may research or generate fixtures; broad findings and done marks require highest-capability review.

## Serial Foundation

| Lane | Exclusive ownership | Deliverable | Depends on | Sidecars |
|---|---|---|---|---|
| S0 architecture/audit | KPF architecture/design/plan docs and coordination state | K0g/K0c boundary, identities, inventory, baselines | none | research sidecars allowed |
| S1 schema/ABI | `src/tool/kernel_plugin_schema/**`, ABI templates, generated-file policy | frozen V1 prefix, generators, compatibility corpus | S0 | fixture generation allowed |

S1 must merge before generated runtime/SDK implementation begins.

## Wave A — Core Runtime And SDKs

| Lane | Exclusive ownership | Deliverable | Dependency |
|---|---|---|---|
| A1 common contract | `src/lib/common/kernel_plugin/**` | IDs, records, validation, receipts | S1 |
| A2 bounded sync | `src/lib/nogc_sync_mut/kernel_plugin/**` | admission, graph, slots, generations, pins | S1/A1 |
| A3 async/noalloc | `src/lib/nogc_async_mut/kernel_plugin/**`, `src/lib/nogc_async_mut_noalloc/kernel_plugin/**` | rings, arenas, requests, cancel/deadline/quiesce | S1/A1 |
| A4 loader/worker | `src/os/smf/kernel_plugin/**` | native/SMF loader adapter, worker transport/supervisor | S1/A1 |
| A5 Rust SDK | `sdk/kernel_plugin/rust/**` | raw ABI and safe wrappers | S1 |
| A6 C/C++ SDK | `sdk/kernel_plugin/c/**`, `sdk/kernel_plugin/cpp/**` | C examples and C++ RAII wrapper | S1 |
| A7 acceptance/fault | new KPF conformance/fault test trees only | ABI, lifecycle, capacity, mutation and crash corpus | S1 |

**Merge gate:** four-language layouts match; strict profile allocates zero after activation; static/native parity; stale handles, full rings, cancellation and generation retirement are non-vacuously tested.

## Wave B — Product Pilot And Closure

| Lane | Exclusive ownership | Deliverable | Dependency |
|---|---|---|---|
| B1 backend adapter | backend plugin model/adapter/transport paths | generated KPF backend facet, retained sessions, caller output | Wave A |
| B2 extended-enum closure | dynamic identity/completeness paths | persistent mapping, required-operation tables, dense tags | S1/A2 |
| B3 security/fuzz | KPF fuzz/fault/check scripts | malformed ABI, trust, signature, ABA, crash tests | Wave A |

**Merge gate:** backend parity and rollback; critical closure rejects Dyn/missing operations; admission fails closed.

## Wave C — Lint

| Lane | Exclusive ownership | Deliverable | Dependency |
|---|---|---|---|
| C0 lint kernel | common/async lint kernel and shared frontend | records, coverage, planner, merge, fixes, verdict | Wave A |
| C1 Simple provider | current Simple lint/check adapter paths | generated rules, semantic snapshots, CLI convergence | C0 |
| C2 Rust provider | Rust tooling worker paths | Cargo/Clippy/rust-analyzer structured adapter | A4/C0 |
| C3 C++ provider | Clang tooling worker paths | compilation DB, clangd/clang-tidy adapter | A4/C0 |
| C4 portable policy | portable rules and mixed fixtures | project/layer/text policies, conflict tests | C0 |

**Merge gate:** mixed workspace deterministic; every required unit/rule/phase receipted; mutation cannot produce false clean; stale fixes rejected.

## Wave D — IDE

| Lane | Exclusive ownership | Deliverable | Dependency |
|---|---|---|---|
| D0 extension facade | editor KPF adapter paths | manifests, activation, commands/events, real workers | Wave A |
| D1 tooling session | editor-neutral workspace/document/language service paths | snapshots, cache, cancellation, protocols | C0/D0 |
| D2 native client | SVIM/Simple IDE integration paths | shared diagnostics/tests/commands | D1 |
| D3 VS Code desktop | desktop TypeScript client paths | thin trusted KPF/LSP client | D1 |
| D4 browser/Wasm client | browser extension/Wasm paths | browser worker, virtual workspace, degradation | D1 |
| D5 conformance | editor-neutral and Extension Host tests | native/desktop/browser parity and crash tests | D1-D4 |

**Merge gate:** stale results cannot publish; authoritative/degraded/unavailable are distinct; clients agree on canonical fixtures; UI survives provider failure.

## Wave E — MDSOC++ And Hardening

| Lane | Exclusive ownership | Deliverable | Dependency |
|---|---|---|---|
| E1 MDSOC++ sealer | MDSOC++ schema/sealer paths | capsule graph, authority, budgets, proof | B2 |
| E2 large pilot | one preselected userland subsystem only | reversible capsule migration | E1 |
| E3 performance | benchmark/instrumentation paths | allocation, latency, RSS, scaling gates | Waves A-D |
| E4 Wasm projection | WIT/component adapter paths | optional isolated placement | S1/A4 |
| E5 public docs/examples | guide and SDK examples only | reproducible migration cookbook | frozen behavior |

**Final merge gate:** all REQ-KPF-001..012 have implementation and executable acceptance evidence; independent reviewer issues PASS; rollback remains available until final product cutover.

## Review Assignment

Each feature lane receives a layer-owner review; each layer lane receives a product-consumer review. The merge owner checks ownership, generated-file provenance, dependency order, and acceptance evidence. The final reviewer checks architecture consistency, non-vacuity, no-GC/noalloc honesty, SCI authority, false-clean prevention, and measured performance before declaring completion.
