# Kernel Plugin Fabric Agent Tasks

**Status:** Active implementation
**Merge owner:** KPF integration owner (highest-capability model)
**Final reviewer:** Independent architecture/verification owner, not an implementation-lane author

## Published Lane Ledger

Audit baseline: integration branch at `67532532552dabb24208b6687e2c23b9ae6947a9`,
including KPF commits through `2157abcbe56` and the landed semantic-check lane.
The requested start `3164fbc39376a2a543f5afa7fa92f1aca6d3d393` is an ancestor.
Published source is not equivalent to a closed gate; runtime-blocked Simple tests remain unverified.

| Lane | Published state | Next owner action |
|---|---|---|
| S0 | Complete for current architecture baseline | Maintain decision/status documents as contracts change |
| S1 | C, Rust, and C++ generators plus append-compatibility/operation-slot checks published; generated Rust/C++ fixture compilation passed | Add the generated Simple binding, complete malformed/layout compatibility corpus, and prove deterministic all-language regeneration from one schema |
| A1 | K0g common contracts published | Add remaining receipt/descriptor coverage only through schema-owned evolution |
| A2 | Fixed slots, exact active-generation pins, static registry, and atomic immediate-predecessor rollback published | Execute rollback/pin/stale-handle scenarios with a compatible Simple runtime and add O(1) counters/scaling evidence |
| A3 | Async runtime, strict noalloc projection, and native allocator-interposition mutation gate published; native gate passed | Execute Simple lifecycle scenarios and add deadline, cancellation-race, quiescence, arena, long-run, and scaling gates |
| A4 | SMF admission plus supervised process-facade worker transport published; native child lifecycle/malformed/crash/timeout gate passed | Add signatures/trust, crash-loop budget, shared placement parity, and executable Simple transport evidence |
| A5 | Rust raw/safe SDK published and runtime tested with Cargo | Keep aligned with the final generated ABI and compatibility matrix |
| A6 | C/C++ examples and non-throwing RAII SDK published and runtime tested | Keep aligned with generated ABI; extend malformed/compatibility corpus |
| A7 | Acceptance scaffolding and closure verifier published | Convert production-dependent red scenarios as modules land; preserve non-vacuity |
| B1 | Backend admission and retained native batch session published; native fixtures passed | Prove bootstrap, static/dynamic/worker parity, production reachability, and rollback |
| B2 | Constructor ID projection, operation-completeness tables, sealed dense tags, and critical `Dyn` rejection published | Execute focused Simple tests and integrate the closure proof with the final schema authority |
| B3 | Partial worker fault groundwork only | Add ABI fuzz, signature/trust, ABA, unload, and crash-loop acceptance corpus |
| C0 | Common records and bounded scheduler published | Add normalized edits/output adapters, cache/invalidation, and full planner/merge behavior |
| C1 | Legacy proof projection plus semantic-by-default `check` on both front doors and explicit `--syntax-only` published | Execute clean/type-error/unresolved-name scenarios, then complete generated rules, snapshots, and shared CLI result projection |
| C2 | Bounded Cargo/Clippy adapter plus typed structured-JSON parsing fix published | Add rust-analyzer live service and executable toolchain mismatch/cancellation corpus |
| C3 | Compile-database/Clang worker contract with exact TU receipts and typed fixes published | Add real clangd/clang-tidy execution, exact toolchain admission, and cache behavior |
| C4 | Not published | Implement portable policies and mixed-workspace conflict fixtures |
| D0 | Editor compatibility facade published | Complete manifest projection and production worker lifecycle integration |
| D1 | Generation-pinned workspace plus versioned `toolingd` document sessions, exact revision/digest checks, supersession cancellation, diagnostic publication, and disconnect cleanup published | Execute focused scenarios with a compatible runtime and add LSP/DAP/test/custom protocol adapters |
| D2 | Native editor tooling client foundation published | Complete SVIM/Simple IDE production cutover and shared diagnostics/tests/commands conformance |
| D3 | VS Code KPF admission/service projection and generated contribution projection published; four focused tests and TypeScript compilation passed | Integrate the production desktop client and shared conformance corpus; retain explicit degraded behavior |
| D4-D5 | Not published | Implement browser/Wasm client and editor-neutral conformance after D1/D3 integration |
| E1 | Deterministic MDSOC++ capsule/facet sealer, budgets, lifecycle order, receipts, migration compatibility, and real IDE/tooling product-generation upgrade owner published | Execute the large-program pilot and mutation-sensitive state migration/publication/drain/rollback receipt proof |
| E2-E5 | Not published as complete lanes | Continue pilot, performance, Wasm, and public documentation only with prerequisite gates preserved |

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

The original dependency rule remains normative. Existing parallel foundation commits must be reconciled through the S1-generated schema before V1 is frozen; publication order does not waive schema ownership.

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
