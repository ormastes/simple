<!-- codex-research -->

# Reusable Async No-GC Kernel Plugin Fabric, Multi-Language Lint/IDE, and MDSOC++

## Provenance

- **Artifact type:** domain research and successor architecture proposal
- **Source:** user-supplied proposal dated 2026-09-03
- **Repository:** `ormastes/simple`
- **Proposal's audited baseline:** `43a4a491c3b5ab8bd350a09a2541a726213053a2`
- **Artifact integration baseline:** PR head `9b0fc60034172e41b6164f92b7e8a7ffd7388a8b`
- **Status:** proposed; this document does not claim implementation, qualification, or release

This artifact preserves the substantive decisions, comparative evidence, architecture,
migration strategy, verification program, and references from the user-provided
proposal. Current repository state must be re-audited before implementation because
the proposal's evidence was gathered at an earlier revision.

## 1. Executive Decision

Create a reusable **Kernel Plugin Fabric (KPF)**: a small, stable nucleus usable by
compilers, IDEs, linters, servers, and large applications. KPF has one logical
contract projected into four placements:

1. **Static closed composition:** generated registry, direct typed calls, whole-program
   optimization, and no hot-path runtime lookup.
2. **Bounded in-process composition:** stable C ABI, admitted and pinned providers,
   caller-owned memory, cached operation tables, and asynchronous batch submission.
3. **Isolated worker composition:** the same interfaces over shared-memory rings or
   framed IPC for untrusted, crash-prone, or toolchain-coupled providers.
4. **Wasm component composition:** an optional portable and sandboxed WIT projection;
   it is not the hard-real-time baseline.

The canonical source should be a compact SDN interface schema, tentatively
`*.kpf.sdn`, which deterministically generates Simple interfaces, a canonical C ABI,
Rust wrappers, C++ RAII wrappers over that C ABI, worker codecs, IDs and fingerprints,
operation masks, conformance fixtures, and documentation.

The first implementation belongs in the no-GC families:

```text
src/lib/common/kernel_plugin/
src/lib/nogc_sync_mut/kernel_plugin/
src/lib/nogc_async_mut/kernel_plugin/
src/lib/nogc_async_mut_noalloc/kernel_plugin/
src/os/smf/kernel_plugin/
src/tool/kernel_plugin_schema/
include/simple_kernel_plugin_v1.h
sdk/kernel_plugin/{c,cpp,rust}/
```

Lint and IDE must become KPF products rather than creating additional loaders or
registries. MDSOC++ reuses KPF composition and lifecycle instead of duplicating them.
Extended enums are reserved for extensible data-constructor families, not provider,
interface, capability, or loader registries.

## 2. K0g and K0c

The generic reusable nucleus and the compiler bootstrap closure are distinct:

| Kernel | Meaning | Contents |
|---|---|---|
| **K0g** | Generic KPF nucleus | fixed IDs, descriptors, status codes, admission, bounded tables, composition receipts, and submit/poll/cancel contracts |
| **K0c** | Simple compiler bootstrap nucleus | K0g plus the minimum parser/type/MIR closure required to rebuild the compiler |

K0g must not import the Simple parser, HIR, MIR, editor, filesystem scanning, JSON,
LSP, or language-specific lint logic. K0c may add compiler-specific closure only when
required by the self-hosting fixed point. An import-closure gate must prevent K0g from
silently absorbing compiler or product dependencies.

## 3. Scope and Non-Goals

### In scope

- one language-neutral contract for Simple, C, C++, and Rust;
- static and dynamic placement behind identical logical interfaces;
- no-GC-first operation plus a strict fixed-capacity/no-allocation profile;
- bounded async submit, poll, cancellation, deadlines, and backpressure;
- immutable generations, quiescence, safe unload, and rollback;
- build-time schema generation and maximal compile/seal-time validation;
- Simple, Rust, and C++ lint providers under one result and coverage model;
- shared native IDE and VS Code tooling services;
- migration of compiler/backend and editor-extension seams;
- integration with SCI/provider composition and extended-enum completeness;
- MDSOC++ composition for large userland products.

### Explicit non-goals

- no Simple/Rust/C++ class, trait object, future, coroutine, closure, or private AST
  crosses a stable boundary;
- no universal cross-language AST and no per-node FFI;
- no arbitrary hot reload without generation pinning and quiescence;
- no runtime compilation or repair of missing production plugins;
- no replacement of LSP, DAP, rust-analyzer, clangd, Cargo, Clippy, or clang-tidy;
- no ECS or dynamic plugin registry in kernel, driver, interrupt, or hard-real-time paths;
- no Wasm prerequisite for the native KPF baseline;
- no new Simple grammar in the first phase.

## 4. Repository Baseline Findings

The proposal found useful but fragmented foundations:

- `nogc_sync_mut.composition` already provides SCI codecs, fixed-width provider query
  records, ABI digests, route generation, and admission concepts.
- the SMF/provider loader already verifies approved paths, artifact digests,
  capabilities, host ABI, interface versions, symbols, sessions, and pins.
- the existing loader remains too product-specific and uses text-heavy policies,
  growable arrays, and linear pin operations; runtime build command synthesis belongs
  in build tooling rather than the loader.
- `nogc_async_mut` provides polling, futures, cancellation, and scheduling concepts,
  but general executors still contain growable collections, dictionaries, linear
  scans, global task IDs/state, and incomplete opaque polling ownership.
- the editor `ExtensionHost` has useful manifests, activation events, registries,
  permissions, disposables, and crash containment, but remains IDE-specific and lacks
  common SCI admission, generations, pins, and real general worker placement.
- Simple lint has a substantial rule corpus but duplicates profiles, registration,
  diagnostics, fixes, CLI behavior, and orchestration. Parse-only or incomplete paths
  can create false-clean outcomes.
- the VS Code extension is a capable shell and should be thinned rather than replaced;
  the native editor/SVIM core should remain the editing/session authority.
- the landed backend plugin C ABI and admission path are the best initial migration
  pilot, but per-operation open/query/finalize/close is too costly for IDE/lint use.

The target steady state is:

```text
load -> admit -> cache operation tables -> open bounded session
     -> submit batches -> poll completions -> quiesce -> close/unload
```

## 5. Comparative External Evidence

| System | Evidence retained | KPF implication |
|---|---|---|
| VS Code Extension Host | lazy activation and local/web/remote host separation protect UI startup and stability | placement and activation are declarative; heavy analysis stays outside UI shells |
| LSP | language/editor decoupling and reusable process services | use LSP at product edges, not as the internal object model |
| rust-analyzer | immutable snapshots, lazy queries, cancellation, small input deltas, isolated proc macros | keep compiler internals provider-local and expose stable serializable facts/results |
| Cargo/rustc JSON | stable CLI-oriented metadata and structured diagnostic streams | use structured workers first; fingerprint exact toolchain, target, features, and build inputs |
| Clang/clangd/clang-tidy | compile-command authority, per-TU scheduling, incremental indexing, modular checks | require `compile_commands.json` for authoritative C++ results and isolate version-coupled APIs |
| LLVM pass manager | one logical pass can be registered statically or dynamically | generate static and dynamic projections from one interface truth |
| COM `QueryInterface` | stable interface IDs and immutable interface set per object | resolve once at admission and cache typed operation tables |
| Linux module versioning/signing | compatibility CRCs and signed-load refusal | reject digest/signature mismatch rather than best-effort invocation |
| Vulkan extension records | versioned prefixes and optional tails | use version/size/reserved fields, not arbitrary native pointer graphs |
| Node-API | stable C ABI with ergonomic language wrappers | C ABI is canonical; wrappers cannot become the binary contract |
| OSGi Declarative Services | declarative graph and lifecycle | seal the graph and use dense slots instead of hot service lookup |
| Wasm Component Model/WIT | typed portable imports/exports and canonical ABI | optional sandboxed placement generated from the same schema |
| SARIF | standardized static-analysis result interchange | export normalized KPF diagnostics to SARIF without making it internal truth |

Consolidated rules are: one interface with several placements; C ABI at native
boundaries; lookup only during admission/session open; coarse batch operations;
provider-private semantic internals; typed incompleteness; exact fingerprints for
unstable tools; immutable generations; separate no-GC and no-allocation claims; and
LSP/JSON only as edge protocols.

## 6. Core Architecture

### One composition and discovery authority

SCI and `SimpleProviderQueryV1` remain the canonical composition and native/SMF
discovery foundations. KPF extends them; it does not introduce a competing loader.

### Closure is separate from placement

```text
closure:   static | complete | dyn
placement: erased | static-direct | static-table | native | smf | worker | wasm
```

A complete graph can use separately packaged native artifacts if all identities and
digests are sealed. An in-process provider may still be runtime-open `dyn`. Critical
logic rejects runtime-open dependencies even when they happen to be local.

### Stable boundary and private internals

Public records contain fixed-width integers, flags, IDs, digests, offsets/lengths into
owned byte arenas, explicit versions/sizes, and opaque generational handles. Private
Simple, Rust, and Clang structures stay behind providers.

### Generated truth

Provider/rule/command catalogs, static registries, enum extension tables, profile
defaults, bindings, WIT, docs, and contribution projections derive from one typed
declaration graph. Manually maintained duplicate registries are migration-only.

### Receipts

Every run records composition and provider generations, requested/provided
interfaces, planned/actual units/rules/facts, reuse/invalidation, incomplete work,
diagnostics/fixes, toolchain identity, timing, queue/arena high-water marks, and
resource counters. No zero-work or zero-analysis path can infer clean without proof.

## 7. Canonical Contract and ABI

Persistent identities include `PluginId`, `InterfaceId`, `OperationId`, `RuleId`, and
canonical names. Dense provider/interface/operation slots are generation-local and
never persisted without the generation digest. Handles contain generation, slot, and
epoch to reject stale reuse and ABA.

Version axes remain separate: runtime ABI, provider query ABI, interface schema,
record layout, implementation version/digest, product composition, toolchain identity,
and payload schema. Major changes require new identities; additive minor changes use
`struct_size` and explicit optional tails.

Native ABI principles:

- one entry symbol per ABI major, such as `simple_kpf_plugin_v1`;
- every record begins with `abi_version` and `struct_size`;
- explicit integer widths, generated size/alignment/offset assertions;
- reserved-zero fields and validated offsets/lengths;
- no C++ ABI, Rust trait object, Simple object, exception, panic, unwind, callback
  closure, GC reference, or allocator-owned graph crosses the boundary;
- caller-owned output buffers/arenas are preferred, with explicit `required_size`;
- queried descriptors and operation tables are immutable for a generation.

Conceptual operations are `open_session`, `submit_batch`, `poll`, `cancel`, `quiesce`,
and `close_session`. Generated language wrappers may expose futures/coroutines, but the
ABI itself remains a request-handle state machine.

## 8. Bounded Async and Memory Model

KPF requires fixed provider/interface/session/request tables, generational slot maps,
bounded submission/completion/event rings, bounded deadline storage, fixed arenas or
chunk pools, and generation pin tables.

Memory profiles:

| Profile | Initialization | Active path |
|---|---|---|
| `StaticNoAlloc` | compile/link-time capacity | no runtime allocation |
| `ArenaOnly` | host-preallocated arenas | bounded arena operations only |
| `NoGcBounded` | allocation during admission/open | no tracing GC; hot allocations forbidden or strictly budgeted |
| `NoGcGeneral` | explicit allocator allowed | no tracing GC; measured and capped |
| `IsolatedManaged` | worker may use its runtime/GC | bounded isolated transport |

Backpressure is typed: `Accepted`, `Coalesced`, `WouldBlock`, `CapacityExceeded`,
`DeadlineExceeded`, or `Rejected`. Full queues never trigger hidden growth.
Cancellation is generational and idempotent. Stale completions cannot publish.
Detached results are explicitly dropped. All table/ring/arena high-water marks are
observable.

Lifecycle is:

```text
Declared -> Indexed -> Admitted -> Prepared -> Starting -> ShadowActive
         -> Published -> Draining -> Retired -> Unloaded
active states -> Faulted -> Disabled | RestartPending | RolledBack
```

Publication swaps a whole compatible generation atomically. The previous generation
remains usable until the new generation passes admission and shadow gates. Unload is
forbidden while requests, sessions, pins, callbacks, or borrowed buffers remain.

## 9. Compile-Time, Seal-Time, and Load-Time Checks

The schema compiler/sealer rejects malformed declarations, duplicate IDs/canonical
names, collisions, missing or ambiguous providers, incompatible versions/digests,
cycles, capability escalation, invalid closure/placement combinations, unbounded
noalloc records, impossible capacity/alignment budgets, concurrency/reentrancy
mismatch, inaccessible required facets, private/native object fields in portable
records, missing extended-enum operations, and critical compositions containing
runtime-open `dyn` dependencies.

Runtime admission repeats integrity-sensitive checks against actual artifacts: allowed
path/root, digest/signature, symbol, ABI/record sizes, provider/build/toolchain identity,
interfaces/operations/capabilities, schema versions, memory and concurrency contracts,
workspace trust, and generation capacity. No operation runs before an admission receipt
exists.

## 10. Unified Multi-Language Lint

Lint is a KPF analysis graph. Language adapters expose named fact capabilities rather
than a universal AST. Portable rules consume normalized facts; language-native rules
run inside the provider and return canonical diagnostics and fixes.

Fact classes include source, tokens, syntax, symbols, types, control/data flow,
effects, borrow/ownership, project graph, and build configuration. Rules declare their
required facts, scope, fix applicability, cost, determinism, and cacheability. The
scheduler computes the minimal fact closure, shares facts among rules, runs independent
read-only rules in bounded parallelism, deterministically sorts output, and records
missing facts and affected rules.

Canonical records include artifact identity, snapshot-bound spans, diagnostics with
related locations, transactional hash-checked edits, rule descriptors, per-unit
analysis state, and a coverage receipt. Verdict truth is distinct from CLI exit policy:

```text
Clean | Warnings | Errors | Incomplete | ToolFailure | Cancelled | TimedOut | NoInput
```

`Clean` requires complete required coverage and no effective findings. Warning-only is
never called clean. Missing facts, skipped targets, malformed output, tool failure, or
zero analyzed inputs cannot silently pass CI/critical profiles.

### Simple

The Simple adapter exposes parse, module/import, HIR/type/effect/ownership, CFG/dataflow,
compiler diagnostics, source maps, and edits. `simple check` becomes a preset/client of
the same kernel and reports required semantic diagnostics by default. A reduced
`--syntax-only` tier remains explicit and cannot imply semantic cleanliness. Existing
rules migrate behind generated descriptors and shadow parity before old registration
tables are deleted.

### Rust

Use Cargo/rustc/Clippy structured JSON workers and rust-analyzer for IDE features.
Receipts bind Cargo metadata, features, target, profile, flags, build scripts, and exact
tool versions. Rules requiring compiler internals run in exact-toolchain workers using
Clippy/rustc internals or `rustc_public`; Rust compiler pointers never cross KPF.

### C/C++

Use clangd for live IDE semantics and clang-tidy for batch/project checks.
`compile_commands.json` is authoritative evidence. Missing/ambiguous commands produce
`Incomplete`, not clean. libclang is optional for narrower stable C integration;
LibTooling and Clang plugins remain version-pinned workers.

### Output and fixes

Human, JSON, LSP, and SARIF outputs derive from identical normalized records. Fixes are
snapshot-hash checked, transactional, conflict-aware, and classified by applicability.
After applying fixes, the kernel reanalyzes and records introduced/removed diagnostics.

## 11. IDE and Tooling Kernel

The existing VS Code extension and native editor/SVIM remain product shells. A shared
`ToolingWorkspace` owns immutable document snapshots, project/build models, language
sessions, diagnostics/fix caches, command/test/debug capability registries,
cancellation, progress, and receipts.

Use LSP for standard editor features, DAP for debugging, an appropriate test protocol
for tests, and a small typed Simple protocol only for rich blocks, plugin inspection,
MDSOC++ graphs, performance receipts, and specialized operations. Native AST/HIR
objects never cross these protocols.

The existing editor host maps through a compatibility adapter:

| Existing editor concept | KPF projection |
|---|---|
| extension string ID | persistent provider ID plus display metadata |
| activation event | sealed declarative activation predicate |
| command/event | typed command or bounded event interface |
| disposable | owned session/subscription handle |
| context key | typed workspace-state record |
| built-in | static provider |
| in-process | admitted native provider |
| worker | real supervised worker |
| directory scan | install/build-time indexed composition |

VS Code becomes a thin client retaining UI-specific custom editors, views, math, and
AI surfaces. Semantic duplication in `extension.ts` is removed after parity; degraded
syntax fallback remains explicit and cannot report semantic clean. Native IDE shells
consume the same tooling session while retaining one buffer/window/undo authority.

## 12. Extended Enums

Extended enums apply to IR operations, language facts, diagnostic evidence, UI nodes,
and other payload-bearing constructor families. They do not represent provider lists,
interface/capability namespaces, loader symbols, lifecycle states, or open ABI status
sets.

Closure mapping:

| Closure | Meaning |
|---|---|
| `Static` | constructors/providers linked and known; direct exhaustive dispatch |
| `Complete` | artifacts may be separate, but the finite catalog and operations are sealed before activation |
| `Dyn` | runtime-open; generic validated dispatch required and forbidden in critical exhaustive logic |

Persistent identity includes owner enum/interface, provider, local case, payload schema,
module ABI, and schema version. The sealer generates dense generation-local tags and
required-operation tables. Persistent storage and wire formats use stable identities,
never bare dense tags. Existing grammar is retained.

## 13. MDSOC++

MDSOC++ means:

```text
MDSOC++ = MDSOC typed ownership/boundaries
        + sealed KPF composition/lifecycle
        + optional ECS inside userland capsules
        + bounded async command/query/event transport
        + capabilities, generations, receipts, and rollback
```

The product kernel owns composition, interface resolution, lifecycle, bounded async,
capability authority, routing, configuration projection, health, metrics, diagnostics,
and receipts. Capsules own coherent feature state, invariants, commands, queries,
events, optional private ECS worlds, migrations, and budgets.

Cross-capsule mutable object references and sibling-private imports are forbidden.
Commands mutate one authoritative owner, queries are read-only by contract, and events
are immutable facts with declared buffering/coalescing. KPF boundaries are coarse;
ordinary calls inside a capsule stay direct. OS kernel, drivers, and interrupts remain
MDSOC-only or use a statically closed generated subset with no dynamic ECS registry.

Initial pilots are the IDE and compiler provider architecture. MDSOC++ must reuse KPF
rather than building a second runtime.

## 14. Migration Program

Migration is incremental and reversible:

```text
Adapt -> Shadow -> Select -> Default/Delete
```

Every subsystem first emits/consumes the new contract, then runs old and new paths on a
bounded corpus, becomes opt-in by composition/profile, and only becomes default after
production reachability, mutation, parity, rollback, and performance evidence.

Recommended milestones:

0. freeze evidence, K0g/K0c, names, IDs, terminology, and current behavior;
1. build schema/canonical ABI generation and cross-language conformance;
2. implement bounded runtime, O(1) pins, arenas, submit/poll/cancel/quiesce;
3. migrate the landed backend plugin as the first production pilot;
4. build canonical lint records, coverage, scheduling, and language providers;
5. adapt the editor host and common tooling session, then thin clients;
6. connect extended-enum completeness and add an MDSOC++ pilot;
7. harden workers, signatures, fuzzing, performance, and optional WIT/Wasm.

No package-wide rename or flag-day rewrite should precede a proven adapter pilot.

## 15. Parallel Ownership Plan

Foundation work is serial: an architecture/audit owner freezes K0g/K0c and naming; a
schema/ABI owner freezes the V1 prefix and owns generated artifacts. Parallel waves
then use exclusive path ownership:

1. **Runtime/SDK wave:** common contracts, bounded sync tables, async/noalloc runtime,
   loader/worker, Rust SDK, C/C++ SDK.
2. **Pilot/security wave:** backend compatibility, extended-enum closure, fuzz/fault
   injection.
3. **Lint wave:** lint kernel, Simple migration, Rust provider, C++ provider,
   cross-language policies.
4. **IDE wave:** editor compatibility facade, native client, VS Code desktop/browser,
   conformance and crash tests.
5. **MDSOC++/hardening wave:** sealer, large-program pilot, performance/memory, docs and
   examples.

Each lane records starting/integration SHAs, owned paths, contracts, generated files,
production caller, negative control, planned/actual tests, resource counters,
rollback/deletion gate, and unsupported cases. Shared schemas and generated registries
have one owner per wave. No lane may weaken a fail-closed rule or claim green from zero
planned/executed cases.

## 16. Verification Strategy

### ABI and schema

- generated `sizeof`, alignment, and offset equality across Simple/C/Rust/C++;
- golden vectors, endian/width checks, truncation/additive compatibility;
- invalid offsets, overflow, unknown required fields/capabilities, reserved bits;
- schema mismatch, malformed descriptors, symbol visibility, no cross-boundary unwind;
- fuzz decode and round-trip properties.

### Runtime and lifecycle

- ring full/backpressure/coalescing, stale slots/tokens/pins, ABA epochs;
- cancellation before/during/after execution, deadlines, fairness, reentrancy;
- provider start/crash/invalid response, drain with live resources;
- unload refusal while pinned, atomic swap, rollback, deterministic replay;
- repeated replacement without unbounded growth.

### No-GC/noalloc

- allocator interception after activation;
- fixed-table/ring/arena high-water and canary checks;
- forbidden allocation/effect scans in strict closure;
- long-run leak/fragmentation and stack/persistent-memory budgets;
- explicit evidence distinguishing `NoGcBounded` from `StaticNoAlloc`.

### Lint

- clean, syntax, semantic, warning-only, partial, no-input, skipped target, malformed
  output, crash, cancellation, timeout, and cache invalidation;
- sabotage and mutation tests proving skipped providers/rules change coverage;
- deterministic output across concurrency levels;
- stale/conflicting fix handling and CLI/LSP/JSON/SARIF parity;
- real Cargo and compilation-database fixtures;
- regression proofs that Simple type/name errors cannot pass and missing C++ build
  configuration cannot yield clean.

### IDE and MDSOC++

- snapshot ordering and stale-result rejection;
- lazy activation and no unrelated worker startup;
- worker crash containment, trust/capability denial, disposal/leak checks;
- native/VS Code/browser conformance where supported;
- extended-enum closure and dense-tag identity;
- sibling-private import rejection, command ownership, state migration, rollback,
  bounded overload, capsule fault isolation, and kernel/driver ECS prohibition.

Cross-platform minimum: Linux x86_64, Windows x86_64, macOS arm64, and a representative
SimpleOS/QEMU static profile. Missing optional toolchains are explicit unsupported or
incomplete evidence, never silently skipped success.

## 17. Performance and Memory Research Targets

Numeric thresholds require Phase-0 baselines. Structural gates apply immediately:

- root help/version starts no ordinary plugin, worker, scan, or runtime compilation;
- erased providers leave no tested hot-path residue;
- static direct uses no registry lookup and is eligible for inlining;
- static table is one bounds check plus one indirect call;
- native dynamic is generation-slot validation plus one indirect batch call;
- strict sealed dispatch allocates zero heap memory;
- no hash/string/semver/path lookup occurs per operation;
- editor changes cancel/coalesce obsolete analysis and cannot queue unbounded versions;
- installed composition startup uses an index/image, not directory scans.

Required measurements include startup/first use, interface resolution count, dispatch
counts, queue full/coalescing, high-water marks, worker RSS/CPU/I/O, planned/executed/
reused/invalidated facts and rules, diagnostic bytes, generation pins/drain time, and
UI-to-diagnostic latency. Benchmarks compare static Simple, native C, Rust, C++, worker,
and legacy backend paths across cold/warm and small/large batches.

Initial baseline-relative targets proposed are ≤1% meaningful regression for coarse
static calls, ≤5% framework overhead for admitted in-process batch calls, zero strict
post-activation allocations, O(1) pin/unpin/cancel, fixed configured memory, and no
steady-state interface lookup.

## 18. Security and Robustness

Capabilities are stable, versioned IDs granting least-authority handles for workspace,
filesystem, network, process/toolchain, UI, semantic query, persistent state, clock,
entropy, and unsafe native access. Configuration cannot raise product ceilings.

Trusted sealed first-party providers may be static/in-process. rust-analyzer, clangd,
Cargo, Clang, and exact-toolchain compiler plugins default to supervised workers.
Untrusted third parties use workers or Wasm. Hard-real-time providers are static closed.

Admission binds canonical manifest, artifact digest/signature, publisher, SDK/toolchain
digest, allowed roots, composition policy, and revocation state. Responses are bounded
and schema validated. Failure taxonomy includes configuration/composition/
compatibility/admission errors, capability denial, resource exhaustion, backpressure,
cancellation, timeout, provider fault, protocol violation, toolchain failure,
incomplete analysis, stale snapshot, state migration failure, and rollback failure.

## 19. Principal Risks and Mitigations

| Risk | Mitigation |
|---|---|
| K0g absorbs compiler/product closure | import-closure checker and negative fixture |
| ABI freezes awkwardly | keep V1 small, append-only generation, backend pilot first |
| universal AST weakens or freezes semantics | portable facts plus provider-native rules |
| unload with live code/state | generations, pins, quiescence, epochs, worker boundary |
| no-GC misrepresented as noalloc | separate memory classes and allocator evidence |
| Rust/Clang API drift | exact-toolchain workers and stable CLI/LSP fallback |
| IDE semantic duplication | one tooling provider and shared conformance corpus |
| extended enum becomes plugin registry | stable descriptors for plugins; enums only for sealed constructors |
| hot service lookup | resolve once and dispatch via dense slots |
| per-node FFI | coarse batches and provider-local semantic graphs |
| parallel schema conflicts | serial freeze and exclusive generated-file ownership |
| partial lint reported clean | typed coverage predicates and mutation/sabotage tests |
| migration breaks existing backend/IDE | compatibility facades and reversible cutover |

## 20. Definition of Done

KPF V1 is complete only when:

- one schema generates ABI-compatible Simple, C, Rust, and C++ bindings;
- static, native, and worker placements pass the same semantic conformance suite;
- strict mode proves zero post-activation allocations;
- interface resolution is confined to admission/session open;
- replacement is safe with in-flight work;
- the current backend runs through both a compatibility adapter and native KPF path;
- Simple, Rust, and C++ lint share one coverage/verdict/diagnostic/fix model;
- no provider/parser/rule failure can yield clean;
- native IDE and VS Code consume the same authoritative tooling records;
- workers contain crashes and enforce capabilities/trust;
- extended-enum Static/Complete closure is sealed and verified;
- one large MDSOC++ userland product is sealed while kernel/drivers remain MDSOC-only;
- ABI, fuzz, fault, performance, memory, bootstrap, and client gates run in CI;
- rollback remains available until final deletion gates;
- public SDK examples build and run in all first-set languages.

## 21. Recommended Order

```text
1. Freeze K0g and the generated ABI schema.
2. Build bounded no-GC async KPF and strict noalloc projection.
3. Migrate the landed backend plugin as the first proof.
4. Build the typed lint kernel and coverage contract.
5. Add Simple, Rust, and C++ providers.
6. Put the existing editor host behind a KPF compatibility facade.
7. Thin native and VS Code clients onto shared tooling services.
8. Connect extended-enum completeness to the sealer.
9. Pilot MDSOC++ on a large userland subsystem.
10. Harden workers, signatures, fuzzing, performance, and optional Wasm.
```

## 22. Repository Evidence from the Proposal

The proposal cited these repository artifacts at audited revision
`43a4a491c3b5ab8bd350a09a2541a726213053a2`:

1. [Minimal bootstrap/configuration-composed dynamic architecture](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/doc/04_architecture/minimal_bootstrap_configuration_composed_dynamic_architecture.md)
2. [Provider contract](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/lib/nogc_sync_mut/composition/provider_contract.spl)
3. [Current provider dispatch](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/app/simple_core/provider_dispatch.spl)
4. [Current SMF provider loader](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/os/smf/provider_loader.spl)
5. [Kernel/plugin migration plan](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md)
6. [Kernel/pluggable partition](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/doc/04_architecture/compiler/plugin_arch/kernel_pluggable_partition.md)
7. [Versioned parameter objects and interfaces](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/doc/05_design/compiler/plugin_arch/versioned_param_objects_and_interfaces.md)
8. [Plugin/versioning research](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/doc/01_research/compiler/plugin_arch/kernel_plugin_versioning_research_2026-08-28.md)
9. [Backend plugin model](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/compiler/00.common/backend_plugin/model.spl)
10. [Backend admission/receipt](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/compiler/00.common/backend_plugin/receipt.spl)
11. [Backend dynamic loader](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/compiler/70.backend/backend_plugin/dynamic_loader.spl)
12. [Backend dynamic adapter](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/compiler/70.backend/backend_plugin/dynamic_adapter.spl)
13. [Backend transport](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/compiler/70.backend/backend_plugin/transport.spl)
14. [Canonical backend C header](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h)
15. [No-GC async overview](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/lib/nogc_async_mut/async.spl)
16. [Embedded async implementation](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/lib/nogc_async_mut/async_embedded.spl)
17. [Simple lint model/config](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/compiler/90.tools/lint/_LintMain/config_and_model.spl)
18. [Simple lint checks](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/compiler/90.tools/lint/_LintMain/lint_checks.spl)
19. [Lint CLI](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/app/io/cli_lint_commands.spl)
20. [Lint parse-failure tracking](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/doc/08_tracking/bug/lint_parse_failure_silently_skips_file_2026-08-01.md)
21. [Lint warning-verdict tracking](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/doc/08_tracking/bug/lint_verdict_says_all_files_clean_with_warnings_2026-09-02.md)
22. [Editor extension contract](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/lib/editor/extensions/contract.spl)
23. [Editor extension host](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/lib/editor/extensions/host.spl)
24. [IDE extension-kernel plan](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md)
25. [VS Code manifest](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/app/vscode_extension/package.json)
26. [VS Code implementation](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/app/vscode_extension/src/extension.ts)
27. [IDE production matrix](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/doc/03_plan/app/editor/editor_ide_production_matrix_2026-05-13.md)
28. [Extended-enum completeness](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/doc/04_architecture/compiler/extension_completeness.md)
29. [Critical closure requirements](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/doc/02_requirements/language/critical_completeness.md)
30. [Persistent dynamic identity](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/compiler/00.common/dynamic_identity/persistent_id.spl)
31. [Dense tag mapping](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/compiler/00.common/dynamic_identity/dense_tag_map.spl)
32. [Static/Complete/Dyn closure](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/src/compiler/00.common/dynamic_identity/closure.spl)
33. [MDSOC architecture and MDSOC+ rules](https://github.com/ormastes/simple/blob/43a4a491c3b5ab8bd350a09a2541a726213053a2/doc/04_architecture/compiler/mdsoc/mdsoc_architecture_tobe.md)

## 23. External Primary References from the Proposal

1. [VS Code Extension Host](https://code.visualstudio.com/api/advanced-topics/extension-host)
2. [VS Code Language Server Extension Guide](https://code.visualstudio.com/api/language-extensions/language-server-extension-guide)
3. [Language Server Protocol 3.17](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/)
4. [VS Code Workspace Trust](https://code.visualstudio.com/docs/editing/workspaces/workspace-trust)
5. [VS Code Web Extensions](https://code.visualstudio.com/api/extension-guides/web-extensions)
6. [rust-analyzer architecture](https://rust-analyzer.github.io/book/contributing/architecture.html)
7. [Cargo external tools](https://doc.rust-lang.org/cargo/reference/external-tools.html)
8. [Clippy: adding lints](https://doc.rust-lang.org/clippy/development/adding_lints.html)
9. [clang-tidy contributing and plugins](https://clang.llvm.org/extra/clang-tidy/Contributing.html)
10. [clangd design](https://clangd.llvm.org/design/)
11. [clangd code walkthrough](https://clangd.llvm.org/design/code)
12. [clangd index](https://clangd.llvm.org/design/indexing)
13. [LLVM new pass-manager plugin registration](https://llvm.org/docs/WritingAnLLVMNewPMPass.html)
14. [COM QueryInterface rules](https://learn.microsoft.com/en-us/windows/win32/com/rules-for-implementing-queryinterface)
15. [Linux external-module versioning](https://docs.kernel.org/kbuild/modules.html)
16. [Linux module signing](https://docs.kernel.org/admin-guide/module-signing.html)
17. [Vulkan extensible structures](https://registry.khronos.org/vulkan/specs/latest/html/vkspec.html)
18. [Node-API ABI stability](https://nodejs.org/api/n-api.html)
19. [OSGi Declarative Services](https://docs.osgi.org/specification/osgi.cmpn/8.0.0/service.component.html)
20. [WebAssembly Component Model: WIT](https://component-model.bytecodealliance.org/design/wit.html)
21. [WebAssembly Component Model: canonical ABI](https://component-model.bytecodealliance.org/advanced/canonical-abi.html)
22. [WebAssembly Component Model: worlds](https://component-model.bytecodealliance.org/design/worlds.html)
23. [SARIF 2.1.0](https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html)

## 24. Research Conclusion

KPF should be a convergence layer, not a replacement project. Preserve SCI/provider
query, the landed backend ABI, editor contribution behavior, existing lint rules,
VS Code UI, native editor/SVIM state ownership, and the compiler provider plan. Extract
their duplicated registration, lifecycle, scheduling, placement, diagnostics, and
receipt concerns into one generated bounded no-GC fabric through reversible adapters.

The highest-priority architecture work is the K0g/schema boundary and bounded async
runtime. The highest-priority correctness work is a proof-carrying lint verdict and
semantic Simple check path. Rust and C++ should initially reuse structured workers and
language servers. MDSOC++ should be introduced only after KPF is proven by the backend,
lint, and IDE pilots.
