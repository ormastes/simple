# Simple Lint, Kernel Plugin Library, IDE, and MDSOC++

## Research, Architecture, Detailed Design, Migration, and Parallel-Agent Plan

> **Provenance:** This research artifact normalizes the user-supplied 2026-09-03 proposal. The proposal audited repository baseline `43a4a491c3b5ab8bd350a09a2541a726213053a2`. This document records proposed decisions and observed evidence; it does not claim implementation completion.

- **Proposal date:** 2026-09-03
- **Audited repository:** `ormastes/simple`
- **Audited baseline:** `43a4a491c3b5ab8bd350a09a2541a726213053a2`
- **Status:** Proposed successor architecture and migration program
- **Primary implementation family:** no-GC async first, with an explicit bounded/no-allocation profile
- **Initial interoperability:** Simple, C, C++, and Rust
- **Initial product pilots:** `simple lint`, `simple check`, Simple IDE/SVIM, VS Code, and compiler/backend providers
- **Architecture term:** MDSOC++ means MDSOC plus sealed plugin composition and optional MDSOC+ data-oriented internals; it is unrelated to the C++ language name.

## 1. Executive Decision

Create one reusable **Kernel Plugin Library / Kernel Plugin Fabric (KPF)** instead of another product-specific loader or registry.

KPF must:

1. retain `src/lib/nogc_sync_mut/composition/` as the canonical SCI, codec, provider-query, and stable-wire foundation;
2. add bounded lifecycle, scheduling, cancellation, generation, and dispatch under `src/lib/nogc_async_mut/kernel_plugin/`;
3. support static-direct, static-table, native dynamic, SMF, worker-process, and optional Wasm Component placements behind the same logical interfaces;
4. generate product registries, composition images, bindings, rule catalogs, and contribution projections from one typed declaration graph;
5. perform duplicate-ID, dependency, compatibility, placement, capability, capacity, and completeness checks at compile or seal time whenever possible;
6. resolve persistent identities once and dispatch through dense generation-local slots thereafter;
7. keep Simple, Rust, and C++ private compiler/object/container layouts behind provider boundaries;
8. provide the common kernel for linting, IDE/tooling, compiler providers, and large MDSOC++ applications.

The deployment profiles are:

| Profile | Purpose |
|---|---|
| Static closed | Generated direct calls/tables, whole-program optimization, no runtime lookup |
| Bounded in-process | Stable C ABI, admitted/pinned providers, caller-owned memory, async batches |
| Isolated worker | Same interfaces over bounded IPC/shared memory for unstable or untrusted tools |
| Wasm component | Optional portable/sandboxed projection generated from the same schema |

Define two nuclei:

| Kernel | Contents |
|---|---|
| K0g | Generic fixed IDs, descriptors, statuses, admission, bounded tables, receipts, submit/poll/cancel |
| K0c | K0g plus the minimum parser/type/MIR closure required for compiler self-hosting |

K0g must not import compiler frontend/IR, editor, repository scanning, JSON/LSP, or language-specific lint code.

## 2. Scope and Non-Goals

### Goals

- One language-neutral component ABI for Simple, C, C++, and Rust.
- Static and dynamic providers under one semantic contract.
- No-GC-first operation with separately proven bounded/no-allocation modes.
- Async submit/poll/cancel, deadlines, backpressure, quiescence, and safe unload.
- Build-time schema generation and seal-time graph verification.
- One lint result/configuration/scheduling model for Simple, Rust, and C++.
- One editor-neutral tooling kernel consumed by native Simple IDE/SVIM and VS Code.
- Migration of current compiler/backend and editor extension mechanisms through adapters.
- Integration with SCI/provider queries and extended-enum completeness.
- MDSOC++ product composition for large userland programs.
- Explicit parallel ownership, merge order, negative controls, and rollback gates.

### Non-Goals

- No universal cross-language AST.
- No private language objects, futures, trait objects, C++ vtables, exceptions, or allocator-owned graphs across the stable boundary.
- No per-token or per-AST-node FFI.
- No runtime compilation or repair of missing production plugins.
- No repository scan, SDN parse, worker startup, or ordinary plugin load for root `--help`/`--version`.
- No runtime-open `dyn:` providers in critical sealed logic.
- No mandatory ECS inside MDSOC++ capsules or ECS in kernel/driver/interrupt paths.
- No new language grammar in the first phase; use typed declarations, existing annotations, SDN compilation, and existing extended-enum syntax.
- No replacement of LSP, DAP, Cargo, Clippy, rust-analyzer, clangd, or clang-tidy.

## 3. Repository Evidence

### Composition and Provider Foundation

The accepted direction is already `simple-core + SimpleCompositionImageV1 + providers`. Relevant local evidence includes:

- `src/lib/nogc_sync_mut/composition/provider_contract.spl`
- `src/lib/nogc_sync_mut/composition/abi_digest.spl`
- `src/lib/nogc_sync_mut/composition/codec.spl`
- `src/lib/nogc_sync_mut/composition/source.spl`
- `src/os/smf/provider_loader.spl`
- `src/os/smf/provider_activation.spl`
- `src/os/smf/dynsmf_session.spl`
- `src/app/simple_core/provider_dispatch.spl`
- `doc/04_architecture/minimal_bootstrap_configuration_composed_dynamic_architecture.md`

Existing strengths include fixed-width provider query records, artifact and ABI checks, capability validation, process-callable symbol proof, retained loader sessions, and generation pins. Remaining generalization gaps include growable/linear pin structures, text-heavy runtime policy, missing common lifecycle/cancellation/backpressure, and runtime build-command synthesis in `DynSmfSession`.

### Compiler Plugin Foundation

The proposal adopts, rather than reopens, the kernel/provider decisions in:

- `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md`
- `doc/04_architecture/compiler/plugin_arch/kernel_pluggable_partition.md`
- `doc/05_design/compiler/plugin_arch/versioned_param_objects_and_interfaces.md`
- `doc/01_research/compiler/plugin_arch/kernel_plugin_versioning_research_2026-08-28.md`
- `src/compiler/00.common/backend_plugin/model.spl`
- `src/compiler/00.common/backend_plugin/receipt.spl`
- `src/compiler/70.backend/backend_plugin/dynamic_loader.spl`
- `src/compiler/70.backend/backend_plugin/dynamic_adapter.spl`
- `src/compiler/70.backend/backend_plugin/transport.spl`
- `src/compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h`

The landed backend ABI, admission receipt, dynamic lease, and runtime bridge are the preferred first migration pilot. KPF should extract reusable mechanisms without a flag-day replacement.

### no-GC Async Foundation

Relevant building blocks exist in:

- `src/lib/nogc_async_mut/async.spl`
- `src/lib/nogc_async_mut/async_embedded.spl`

The general executor/runtime is not yet sufficient for the strict plugin hot path because current implementations include growable arrays, dictionaries, linear scans/timers, global IDs/state, unreclaimed cancellation IDs, and externally managed pending futures. KPF should reuse concepts while introducing generational slots, bounded rings, fixed arenas, and an allocation-free sealed run phase.

### Editor and IDE Foundation

Relevant evidence includes:

- `src/lib/editor/extensions/contract.spl`
- `src/lib/editor/extensions/host.spl`
- `doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md`
- `src/app/vscode_extension/package.json`
- `src/app/vscode_extension/src/extension.ts`
- `doc/03_plan/app/editor/editor_ide_production_matrix_2026-05-13.md`
- `doc/04_architecture/app/tools/svim.md`

The current editor host already has manifests, activation events, registries, permissions, disposables, and crash-loop containment. The VS Code extension and native editor are valuable shell/editor foundations. They are not yet a shared tooling kernel: worker execution is incomplete, lifecycle and admission differ from SCI/provider generation, and semantic analysis is duplicated in shell-specific paths.

The migration strategy is preservation plus extraction: keep editor authority and UI features, make the host a compatibility client of KPF, and move heavy analysis to shared language/tooling sessions.

### Lint Foundation and Correctness Gaps

Relevant evidence includes:

- `src/compiler/90.tools/lint/`
- `src/compiler/90.tools/lint/_LintMain/config_and_model.spl`
- `src/compiler/90.tools/lint/_LintMain/lint_checks.spl`
- `src/app/io/cli_lint_commands.spl`
- `doc/08_tracking/bug/check_silently_passes_type_errors_parse_only_2026-09-01.md`
- `doc/08_tracking/bug/lint_parse_failure_silently_skips_file_2026-08-01.md`
- `doc/08_tracking/bug/lint_verdict_says_all_files_clean_with_warnings_2026-09-02.md`

The rule corpus is useful, but registration, profiles, scheduling, configuration, diagnostics, fixes, and output are duplicated or hand maintained. A trustworthy result must carry planned/actual files, rules, phases, facts, skips, provider/toolchain identity, cache decisions, diagnostics, fixes, cancellation, and an explicit verdict. Warning-only, no-input, unavailable facts, parser failure, and tool failure must never become false clean results.

### Extended Enums and MDSOC+

Relevant evidence includes:

- `doc/04_architecture/compiler/extension_completeness.md`
- `doc/02_requirements/language/critical_completeness.md`
- `src/compiler/00.common/dynamic_identity/persistent_id.spl`
- `src/compiler/00.common/dynamic_identity/dense_tag_map.spl`
- `src/compiler/00.common/dynamic_identity/closure.spl`
- `test/01_unit/compiler/frontend/enum_extension/enum_extension_grammar_spec.spl`
- `doc/04_architecture/compiler/mdsoc/mdsoc_architecture_tobe.md`

Extended enums are appropriate for sealed data-constructor families, not global plugin discovery, capability identity, or ABI status namespaces. MDSOC++ retains MDSOC boundaries, permits optional ECS/data-oriented internals inside userland capsules, and adds sealed KPF composition, bounded async transport, capability authority, generations, receipts, and rollback.

## 4. External Architecture Findings

The proposal draws these conclusions from primary external systems:

| System | Adopt | Avoid |
|---|---|---|
| VS Code | Declarative contributions, lazy activation, UI/workspace placement, host isolation | UI-specific analysis truth |
| LSP/DAP | Standard editor/debug edge protocols | Using JSON-RPC as the internal object model |
| Cargo/rustc/Clippy | Structured CLI/JSON and exact toolchain receipts | Linking unstable internals into K0g |
| rust-analyzer | Immutable snapshots, lazy queries, cancellation, reusable server | Exporting private HIR/runtime layouts |
| clangd/clang-tidy | Compilation-database authority, worker isolation, structured diagnostics/fixes | Pretending Clang C++ APIs are cross-version stable |
| LLVM pass manager | Same logical extension statically or dynamically registered | Toolchain-coupled APIs as a stable product ABI |
| COM QueryInterface | Stable IDs queried once and cached | Per-call discovery and unnecessary reference-count complexity |
| Linux modules | Exact compatibility/signature refusal | Best-effort invocation after mismatch |
| Vulkan structures | Version/size prefixes and optional append-only tails | Portable raw pointer chains |
| Node-API | Canonical C ABI with language wrappers | Making wrappers the binary contract |
| OSGi DS | Declarative dependencies and lazy lifecycle | Hot-path service lookup |
| Wasm Component Model/WIT | Optional portable typed sandbox generated from one schema | Requiring Wasm for trusted static/hard-RT paths |
| SARIF | Common CI/static-analysis interchange | Separate diagnostic truth |

## 5. Core Architecture Rules

1. SCI remains the single immutable composition authority.
2. `SimpleProviderQueryV1` remains the canonical native/SMF discovery boundary.
3. Closure and placement are independent axes.
4. Stable boundaries contain fixed-width records, offsets/lengths, IDs/digests, and opaque releasable handles only.
5. Static/direct placement is preferred for trusted hot paths; dynamic placement is policy-driven.
6. Sealed bounded profiles use preallocated generational slots, rings, and arenas with explicit overload outcomes.
7. Physical providers are coarse deployment/trust units; rules and queries are fine scheduling units.
8. Unknown or incomplete work fails closed and cannot produce a clean verdict.
9. Registries, bindings, rules, contribution tables, documentation indexes, and enum operation tables are generated from one typed declaration graph.
10. Every run emits deterministic receipts describing selection, coverage, cache behavior, invalidation, failures, timing, and bounded resource counters.

## 6. Proposed Module Structure

```text
src/lib/nogc_sync_mut/composition/          # canonical existing SCI/wire core
src/lib/common/kernel_plugin/               # wire-neutral IDs/contracts
src/lib/nogc_sync_mut/kernel_plugin/        # admission/composition/fixed tables
src/lib/nogc_async_mut/kernel_plugin/       # bounded async lifecycle/dispatch
src/lib/nogc_async_mut_noalloc/kernel_plugin/
src/os/smf/kernel_plugin/                   # native/SMF/worker placement
src/tool/kernel_plugin_schema/              # SDN compiler/sealer/generators
include/simple_kernel_plugin_v1.h
sdk/kernel_plugin/c/
sdk/kernel_plugin/cpp/
sdk/kernel_plugin/rust/
src/lib/tooling_kernel/
src/compiler/90.tools/lint/kernel/
src/lib/editor/kernel_plugin/
src/lib/mdsocpp/
```

Do not rename/move the existing composition package first. Add facades and adapters, prove pilots, then reconsider source ownership.

## 7. Contract and ABI Design

### Identity and Versions

Persistent IDs are canonical tuple hashes for plugins, interfaces, operations, rules, capabilities, and extended-enum cases. Dense slots are generation-local, never persistent, and valid only with the generation digest.

Version axes remain separate:

- kernel runtime ABI;
- provider query ABI;
- interface schema major/minor;
- wire-record version/size;
- provider implementation semver/build digest;
- product SCI digest/version;
- toolchain identity;
- payload schema ABI.

Changing an implementation without changing an interface does not require a kernel rebuild. Schema-major changes require adapters or consumer rebuilds.

### Canonical Native Boundary

- one C entry symbol per ABI major, such as `simple_kpf_plugin_v1`;
- every public record begins with `abi_version` and `struct_size`;
- explicit integer widths, generated alignment/offset assertions, reserved-zero rules;
- UTF-8 slices with explicit lengths, fixed IDs on hot paths;
- caller-owned output buffers or arenas with `required_size`;
- immutable dynamic descriptors for a loaded generation;
- no exceptions/panics/unwind across the ABI.

Generated Simple, Rust, and C++ layers are safe facades over the canonical C ABI, not independent contracts.

### General Async Operation Contract

The stable ABI exposes a state machine rather than language-native futures:

```text
open_session
submit_batch -> Accepted | WouldBlock | CapacityExceeded | Rejected
poll         -> completion page
cancel       -> Requested | AlreadyTerminal | Unknown/Stale
quiesce      -> bounded drain/cancel
close        -> release idle session
```

Inputs remain pinned or are explicitly copied into admitted memory. Outputs use host-owned storage or explicit release handles. Every offset and length is validated.

## 8. Bounded Runtime and Lifecycle

Required structures:

```text
GenerationalSlotMap<PluginState>
GenerationalSlotMap<SessionState>
GenerationalSlotMap<RequestState>
BoundedMpscRing<RequestEnvelope>
BoundedMpscRing<CompletionEnvelope>
BoundedRing<EventEnvelope>
bounded deadline heap or timer wheel
fixed/chunk payload and diagnostic arenas
GenerationPinTable
```

Profiles distinguish allocation policy:

| Profile | Policy |
|---|---|
| NogcGeneral | No tracing GC; allocator allowed and measured |
| NogcBounded | Allocate during create/prepare; no hidden growth after seal |
| NogcStatic / StaticNoAlloc | Compile-time/fixed capacities; zero runtime heap |

Lifecycle:

```text
Declared -> Indexed -> Admitted -> Prepared -> Starting -> ShadowActive
         -> Published -> Draining -> Retired -> Unloaded
active state -> Faulted -> Disabled | RestartPending | RolledBack
```

Publication swaps a whole compatible generation atomically. Unload requires zero sessions, requests, callbacks, borrowed buffers, and pins. The previous generation remains selectable until the candidate passes admission and shadow gates.

Capabilities are concrete scoped leases, not ambient access. Worker/Wasm placements receive serialized authority handles. Critical profiles reject wildcard resource authority.

## 9. Compile-Time, Seal-Time, and Runtime Checks

Compile/seal-time checks include:

- malformed declarations and schemas;
- duplicate/colliding IDs and aliases;
- missing/ambiguous providers and operations;
- incompatible major/minor/schema digests;
- static dependency cycles;
- critical graphs containing runtime-open `dyn` paths;
- capability escalation;
- invalid noalloc/threading/reentrancy placement;
- impossible memory/alignment/capacity budgets;
- incomplete extended-enum operation tables;
- unreachable required facets;
- checking profiles with zero executed work.

Load-time checks include canonical path/root, artifact digest/signature, target, entry symbol, descriptor prefix, toolchain/build identity, capabilities, operations, schemas, memory/concurrency contract, and workspace trust.

Runtime checks include stale generational handles, backpressure, deadlines, cancellation, malformed responses, crashes, drain, and quiescence.

## 10. Unified Lint Kernel

Lint becomes a KPF analysis graph with language adapters exposing named fact capabilities rather than one universal AST.

Fact families include source text, tokens, syntax, symbols, types, control/data flow, effects, ownership, project graph, and build configuration. Rules declare required/optional facts, scope, determinism, cost, fix support, and profile eligibility. The scheduler computes the minimal fact closure, shares facts, runs independent rules within budgets, sorts output deterministically, records missing facts, and invalidates only affected nodes.

Canonical results include:

- artifact/snapshot identity;
- provider/rule/toolchain identity;
- normalized diagnostics and related locations;
- transactional hash-checked edits and conflict groups;
- requested/planned/analyzed/skipped files;
- selected/executed/failed rules;
- missing facts;
- cache and invalidation receipts;
- verdict.

Verdicts are explicit: `Clean`, `Warnings`, `Errors`, `Incomplete`, `ToolFailure`, `Cancelled`, `TimedOut`, and `NoInput`. Exit policy is a projection; truth is not inferred from an exit code or `error_count == 0`.

### Simple Adapter

- expose parser, module/name, type/effect/ownership, CFG/dataflow, diagnostics, and source-map queries;
- make default `simple check` semantic, retaining explicitly labeled `--syntax-only` reduced coverage;
- fix semantic enforcement blockers and census existing violations before promotion;
- replace duplicated rule/default/name tables with generated declarations;
- converge `check`, `lint`, compiler, CLI, and LSP diagnostics;
- include parser/build identity and actual fact coverage in receipts.

### Rust Adapter

- use `cargo metadata`, Cargo/rustc/Clippy JSON, and rust-analyzer first;
- run custom rustc/Clippy/rustc_public integrations only in exact-toolchain workers;
- preserve spans, children, suggestions, and applicability;
- record workspace, features, target, flags, toolchain, malformed output, timeout, and skipped targets;
- never export Rust compiler objects across KPF.

### C/C++ Adapter

- use clangd for IDE and clang-tidy for batch/project lint;
- require `compile_commands.json` or explicitly report fallback/incomplete configuration;
- keep LibTooling/Clang AST integrations in version-pinned workers;
- use libclang only for narrower stable C integration;
- record compiler resource directory, target/sysroot, defines, include paths, standard, modules, and translation-unit identity.

The same normalized records feed human CLI, JSON, LSP, and SARIF output.

## 11. IDE and Tooling Architecture

The shared `ToolingWorkspace` owns composition/generation, immutable document snapshots, project/build models, language sessions, diagnostics/fix caches, command/test/debug registries, cancellation, progress, and receipts.

Use LSP, DAP, and test protocols where applicable. Use a small typed Simple protocol only for rich blocks/math, composition inspection, MDSOC++ graphs, performance receipts, and specialized compiler/verification operations.

VS Code remains a rich UI shell. Its activation root should load generated contributions, create a tooling client, register generic adapters, and retain shell-specific views/custom editors/webviews. Duplicated semantic fallback is removed after parity; any remaining syntax-only fallback is clearly degraded and cannot publish semantic clean status.

SVIM/Simple IDE retains buffer/window/tab/anchor/undo authority and consumes the same tooling protocol/results. Diagnostics attach to snapshots/anchors; tooling cannot mutate text directly. Static in-process tooling remains available for small products, while desktop products may use daemon/worker placement.

Editor extensions split UI contributions from heavy workspace/language providers. One package may have differently placed components.

## 12. Extended Enums

Use extended enums for semantic constructor families such as IR nodes, typed tooling requests, fact variants, and contribution kinds. Do not use them for the global provider list, interface IDs, capabilities, loader symbols, or open ABI status codes.

Closure semantics:

| Region | Closure | Dispatch |
|---|---|---|
| Ordinary | defining module compile | native dense tag |
| `complete:` | product composition seal | generated dense extension table |
| `dyn:` | runtime open | persistent qualified ID resolved to dynamic slot |

Persistent identity includes owner enum/interface, provider ID, local case identity, payload schema ABI, and module ABI. Serialization uses persistent identity, never a dense tag. The sealer generates required-operation tables, rejects collisions/missing operations, incorporates extension sets into action keys, and makes exhaustiveness aware of selected complete cases. Critical exhaustive paths reject runtime-open cases.

## 13. MDSOC++

```text
MDSOC++ = MDSOC typed ownership and boundaries
        + optional capsule-local ECS/data-oriented internals
        + sealed KPF composition
        + bounded no-GC async command/query/event transport
        + capability authority, generations, receipts, and rollback
```

The product kernel owns only composition, resolution, lifecycle, bounded scheduling, authority, routing, configuration projection, health, metrics, and receipts. Capsules own coherent feature state, commands, queries, events, migrations, invariants, and optional ECS worlds.

Rules:

- import contracts, not sibling-private implementations;
- declare required/provided interfaces;
- reject cycles unless modeled as bounded asynchronous feedback;
- commands mutate one authority; queries are read-only;
- events are immutable and have declared buffering/coalescing policy;
- no cross-capsule mutable object references;
- persistent schemas version independently;
- keep hot internal calls direct;
- runtime-open plugins remain outside critical static proofs.

MDSOC++ is intended for large IDE/compiler/server/enterprise products. Kernel, driver, interrupt, and hard-real-time paths remain MDSOC-only or use a static closed KPF subset with proven capacities.

## 14. Migration Program

Use four steps for every subsystem:

```text
Adapt -> Shadow -> Select -> Default/Delete
```

Each migration preserves the prior generation/path until production reachability, parity, mutation sensitivity, rollback, and resource gates pass.

### Phase 0 — Evidence and Non-Vacuity

Freeze repository/toolchain identities, conflict-marker state, current lint/check/IDE/provider behavior, planned/actual counts, and startup/allocation/dispatch/RSS baselines. Broken semantic fixtures, warning-only runs, zero-input runs, and removed registrations must fail appropriately.

### Phase 1 — Contracts and Declaration Graph

Add KPF facades, stable IDs/versions/descriptors, operation/diagnostic/edit/receipt schemas, SDN compiler, generated bindings/registries, and graph compatibility validation. Round-trip fixed vectors in Simple/C/Rust/C++; reject private types and malformed compatibility cases.

### Phase 2 — Bounded no-GC Runtime

Implement generational slots, rings, arenas, cancellation, deadlines, lifecycle, generations, direct/table transports, deterministic scheduler, and fault providers. Prove stale-handle safety, backpressure, cancellation, rollback, parity, and zero post-seal allocation in the strict profile.

### Phase 3 — Native/SMF and Backend Pilot

Adapt existing provider query/loader and backend ABI, replace linear pins, retain sessions, move build synthesis out of runtime, support caller-owned output, and publish loader receipts. Prove incompatibility rollback, unload safety, no runtime compiler invocation, and static/dynamic parity.

### Phase 4 — Unified Diagnostics, Fixes, and Receipts

Implement normalized records, transactional edits, verdict state machine, deterministic rendering, and human/JSON/LSP/SARIF projections. Distinguish warning, incomplete, no-input, stale, timeout, and crash outcomes.

### Phase 5 — Simple Lint Shadow Migration

Generate rule descriptors/defaults, wrap existing rules, introduce fact planning, compare old/new paths, and remove hand-maintained duplicate authorities after parity.

### Phase 6 — Semantic `simple check`

Fix semantic enforcement blockers, expose semantic providers, census current violations, make semantic checking the default, and retain explicitly reduced `--syntax-only` behavior.

### Phase 7 — Rust Workers

Implement worker supervision, Cargo/rustc/Clippy JSON ingestion, rust-analyzer brokering, exact identity/cache keys, output limits, cancellation, timeout, and crash containment.

### Phase 8 — C/C++ Workers

Implement compilation-database discovery, clang-tidy and clangd adapters, optional libclang, exact toolchain admission, and snapshot-correct fix mapping.

### Phase 9 — Editor Host Adapter

Map manifests, activation, commands, events, lifetimes, permissions, contexts, worker entrypoints, and generated contribution tables onto KPF.

### Phase 10 — Tooling Sessions

Implement immutable document snapshots/deltas, workspace/project/build models, language sessions, protocol adapters, caches, cancellation by document version, and embedded/daemon modes.

### Phase 11 — IDE Cutover

Thin VS Code and add the native tooling client while preserving UI/editor authority. Prove capability parity, explicit fallback, lazy worker startup, and matching command/test behavior.

### Phase 12 — Compiler Provider Adapter

Adapt `CompilerDriverV1`, then one low-risk backend, preserving SCI/provider-query authority. Prove no unrelated backend imports, incremental closure rebuild, static/dynamic parity, and zero ordinary provider load for help/version.

### Phase 13 — MDSOC++ Pilots

Add the facade/rules, command/query/event interfaces, capsule graph validation, migrations, and at least two large-program pilots without duplicating the runtime.

### Phase 14 — Optional Wasm Component Placement

Generate WIT from canonical schemas, map capabilities/resources/async operations, and prove parity and containment.

### Phase 15 — Default Cutover and Cleanup

Make common lint/tooling/lifecycle authorities default, delete duplicate registries/build synthesis/fallbacks after gates, publish SDKs/compatibility policy, and run full bootstrap/security/performance/rollback matrices.

## 15. Parallel-Agent Plan

### Coordination

Every lane records starting and integration SHAs, owned paths, consumed/produced contracts, generated files, production caller, negative control, tests planned/run, performance counters, rollback gate, and unsupported cases. Shared V1 schemas and generated registries have one owner per wave. Cross-owned changes use requests and failing fixtures.

### Waves

| Wave | Parallel ownership | Ordered integration |
|---|---|---|
| W0 Evidence | baselines, non-vacuity, architecture inventory, malformed scans | freeze evidence revision |
| W1 Contract | V1 schema, diagnostics/edits, receipts, generator, graph sealer, enum requirements | schema -> records -> generator -> sealer |
| W2 Runtime | bounded containers, scheduler, lifecycle, native/SMF, worker, fault and perf harnesses | containers -> scheduler -> lifecycle -> transports |
| W3 Lint | catalog/planner, Simple migration, semantic provider, Rust/C++ workers and IDE brokers, output adapters | common catalog owns generated registry |
| W4 IDE | host adapter, tooling session, VS Code shell, SVIM client, fault/latency tests | adapter/protocol before shell cutover |
| W5 Compiler/MDSOC++ | compiler adapter, enum integration, MDSOC++ facade/pilots, overhead matrix | common KPF contracts remain authoritative |
| W6 Wasm/Release | WIT/host, more provider families, legacy deletion, convergence/rollback/docs | release only after verification evidence |

Recommended lane ownership mirrors the proposal’s A0–A29 / S0–E4 split: architecture/integration, evidence, schema, generation, sealer, bounded containers, scheduler, lifecycle, transports, diagnostics, receipts, enum compiler, lint catalog, language adapters, IDE adapters/clients, compiler adapter, MDSOC++, security/fuzz, performance, tests/release, and documentation.

## 16. Acceptance and Test Strategy

### Contract and ABI

- golden vectors and size/alignment/offset equality across Simple/C/Rust/C++;
- additive minor and truncated descriptor compatibility;
- malformed offsets, overflows, reserved fields, unknown requirements, and digest mismatch;
- fuzz decoding and differential round trips;
- no unwind or private language type at boundaries.

### Graph and Seal

- duplicate IDs/aliases, missing/ambiguous providers, incompatible versions, cycles;
- critical + `dyn` rejection, capability escalation, capacity failure;
- enum identity collision and operation incompleteness;
- deterministic output independent of declaration order;
- one-provider specialization and production reachability.

### Runtime

- full rings, backpressure, coalescing, stale slots/tokens/pins;
- cancellation races and deadlines;
- provider start/crash/invalid output;
- drain/unload with live requests/listeners/buffers;
- atomic generation swap and rollback;
- repeated reload without unbounded growth;
- deterministic replay and noalloc instrumentation.

### Lint

- clean, syntax, semantic/name/type errors, warning-only, multi-diagnostic;
- safe/maybe/conflicting/stale fixes;
- suppression, unknown rule, no input, skipped targets, missing build configuration;
- cancellation, timeout, crash, malformed output, and cache invalidation;
- equivalent human/JSON/LSP/SARIF records;
- sabotage/mutation proving removed rules/providers change coverage and verdict;
- repository-scale non-superlinear target indexing.

### IDE

- document versioning and stale-result rejection;
- lazy activation and no unrelated worker startup;
- multi-root mixed-language workspaces;
- reconnect/restart and degraded fallback labeling;
- command/fix/test/debug parity between native and VS Code clients;
- crash containment and complete deactivation disposal;
- generated contribution mismatch gate.

### Extended Enum and MDSOC++

- ordinary/complete/dyn construction and qualification;
- order-independent persistent IDs and nonpersistent dense tags;
- payload schema invalidation and critical wildcard rejection;
- sibling-private import prohibition, one mutation owner, query purity;
- optional dependencies, event cycles, migration/rollback, direct specialization;
- bounded overload and capsule fault isolation.

### Cross-Platform

At minimum: Linux x86_64, Windows x86_64, macOS arm64, and a representative SimpleOS/QEMU static profile. Missing optional language toolchains are explicit incomplete/unsupported lanes, never silent green.

## 17. Performance and Memory Requirements

Measure baselines before fixing absolute thresholds. Structural gates are immediate:

- root help/version loads no ordinary provider, worker, scan, or runtime compiler;
- erased providers leave no selected-path code/data/dispatch residue;
- static-direct has no registry/hash/version work;
- static-table is one bounds check plus one indirect call;
- admitted native dispatch is generation-slot validation plus one indirect batch call;
- strict sealed dispatch allocates zero heap memory;
- lint recomputes only invalidated facts/rules;
- obsolete editor work is cancelled/coalesced without unbounded queues;
- worker framing is bounded.

Required counters cover startup/first-use, resolution, dispatch placement, ring operations, task/request high-water marks, arena bytes, worker RSS/CPU/I/O, files/facts/rules planned/executed/reused/invalidated, diagnostics/fixes, pins/drain duration, cache serialization, and UI-to-diagnostic latency.

Performance claims record repository revision, binary/provider/composition digests, toolchains, host/OS, profile/placement, cache state, corpus, iterations/warmup, observer mode, latency distribution, and allocation/RSS evidence.

## 18. Security, Robustness, and Operations

- manifests/SCI remain inert;
- exact artifacts/digests/signatures and approved roots are admitted;
- native providers default to trusted products; untrusted providers default to worker/Wasm;
- every response is schema/bounds validated;
- authority cannot exceed the product ceiling;
- crash-loop state is generation scoped;
- repeated failure disables only the provider/generation;
- configuration cannot execute code or silently choose incompatible fallback;
- state migration is transactional and declares rollback compatibility;
- operational inspection exposes composition, generations, bindings, placement, authority, budgets/high-water marks, health, lint coverage, degradation, and cache/admission reasons.

Retry policy distinguishes deterministic configuration failures, normal cancellation/stale snapshots, bounded worker restarts, protocol violations, timeouts, and critical-provider failures. Weaker providers are never substituted silently.

## 19. Immediate First Slice

The smallest end-to-end proof is:

1. define common IDs, closure/placement, diagnostics, edits, receipts, and lint-provider V1 records;
2. generate a static registry for `lint.common.text` and a small `lint.simple.legacy` adapter;
3. implement bounded direct/table dispatch and a fixed diagnostic arena;
4. implement `Clean`, `Warnings`, `Errors`, `Incomplete`, and `NoInput`;
5. shadow old/new lint paths on clean, warning, error, parse-error, and zero-input fixtures;
6. ensure warning-only cannot render clean;
7. project identical records to human, JSON, and minimal LSP output;
8. generate one VS Code contribution;
9. consume the same diagnostic record from one native/SVIM probe;
10. measure allocation and direct/table overhead.

This slice intentionally defers dynamic loading, Rust, C++, and full semantic checking. The next slice adds the Simple semantic provider; Rust and C++ workers can then proceed in parallel.

## 20. Definition of Done

KPF/MDSOC++ v1 is complete only when:

- one canonical schema generates ABI-compatible Simple/C/Rust/C++ bindings;
- static, native, and worker profiles pass one conformance suite;
- strict mode proves zero allocations after activation;
- resolution occurs only at admission/session open;
- generation replacement is safe with in-flight work;
- backend behavior works through both compatibility and native KPF providers;
- Simple, Rust, and C++ lint share one coverage/verdict/diagnostic/fix model;
- no parser/provider/rule failure can yield clean;
- native IDE and VS Code consume authoritative shared tooling sessions;
- workers contain crashes and enforce trust/capabilities;
- complete extended-enum closure is checked by the sealer;
- at least two large MDSOC++ userland pilots pass rollback and performance gates while kernel/drivers remain MDSOC-only;
- ABI, fuzz, fault, bootstrap, memory, performance, client-conformance, and rollback gates run in CI;
- public SDK examples build and run for all initial languages.

## 21. Primary External References

- VS Code Extension Host: <https://code.visualstudio.com/api/advanced-topics/extension-host>
- VS Code Language Server Extension Guide: <https://code.visualstudio.com/api/language-extensions/language-server-extension-guide>
- Language Server Protocol 3.17: <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/>
- VS Code Workspace Trust: <https://code.visualstudio.com/docs/editing/workspaces/workspace-trust>
- VS Code Web Extensions: <https://code.visualstudio.com/api/extension-guides/web-extensions>
- Cargo external tools: <https://doc.rust-lang.org/cargo/reference/external-tools.html>
- rustc JSON output: <https://doc.rust-lang.org/rustc/json.html>
- Clippy development: <https://doc.rust-lang.org/clippy/development/adding_lints.html>
- rust-analyzer architecture: <https://rust-analyzer.github.io/book/contributing/architecture.html>
- Clang tooling: <https://clang.llvm.org/docs/Tooling.html>
- clang-tidy: <https://clang.llvm.org/extra/clang-tidy/>
- JSON compilation database: <https://clang.llvm.org/docs/JSONCompilationDatabase.html>
- clangd design: <https://clangd.llvm.org/design/>
- LLVM new pass manager: <https://llvm.org/docs/NewPassManager.html>
- COM QueryInterface rules: <https://learn.microsoft.com/en-us/windows/win32/com/rules-for-implementing-queryinterface>
- Linux external modules: <https://docs.kernel.org/kbuild/modules.html>
- Linux module signing: <https://docs.kernel.org/admin-guide/module-signing.html>
- Vulkan extensible structures: <https://registry.khronos.org/vulkan/specs/latest/html/vkspec.html>
- Node-API ABI stability: <https://nodejs.org/api/n-api.html>
- OSGi Declarative Services: <https://docs.osgi.org/specification/osgi.cmpn/8.0.0/service.component.html>
- WebAssembly Component Model WIT: <https://component-model.bytecodealliance.org/design/wit.html>
- WebAssembly Canonical ABI: <https://component-model.bytecodealliance.org/advanced/canonical-abi.html>
- WebAssembly worlds: <https://component-model.bytecodealliance.org/design/worlds.html>
- SARIF 2.1.0: <https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html>

## 22. Recommendation

Proceed with KPF as a convergence layer, not a replacement project. Preserve SCI/provider query, editor contributions, existing lint rules, VS Code UI, SVIM editor authority, and compiler providers. Move duplicated lifecycle, registration, scheduling, diagnostics, placement, and receipt concerns into one generated bounded no-GC kernel through compatibility adapters and shadow cutovers.

Prioritize the common verdict/coverage model and Simple semantic checking for correctness, and the generated contract graph plus bounded async runtime for architecture. Use workers and established tooling for Rust and C++ first. Introduce MDSOC++ as a reusable facade only after lint and IDE pilots prove the common kernel.
