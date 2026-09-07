# Simple Lint, Kernel Plugin Library, IDE, and MDSOC++
## Research, Architecture, Detailed Design, Migration, and Parallel-Agent Plan

- **Date:** 2026-09-03
- **Repository inspected:** `ormastes/simple`
- **Repository revision used for the baseline:** `43a4a491c3b5ab8bd350a09a2541a726213053a2`
- **Status:** proposed successor design; implementation has not been claimed
- **Primary implementation language:** Simple, under the no-GC async library family first
- **Interoperability targets:** Simple, Rust, and C++
- **Primary product pilots:** `simple lint` / `simple check`, Simple IDE + SVIM + VS Code shell, and the Simple compiler/provider architecture
- **Architecture name introduced here:** **MDSOC++** (“MDSOC Plus-Plus”; unrelated to the C++ language name)

---

## Executive decision

Simple already has most of the *pieces* needed for a strong plugin architecture, but they are split among three independently evolving systems:

1. `std.nogc_sync_mut.composition`, `SimpleCompositionImageV1`, `SimpleProviderQueryV1`, and the SMF/native provider loader;
2. the editor `ExtensionHost`, its SDN manifests, activation events, registries, permissions, disposables, and crash-loop containment;
3. the compiler-kernel/provider architecture described in the 2026-08-30 plan.

The correct next step is **not** to build another loader or another registry. The correct step is to create a reusable **Kernel Plugin Library** that:

- keeps `std.nogc_sync_mut.composition` as the canonical stable wire/composition foundation;
- adds a bounded no-GC async lifecycle, scheduling, cancellation, generation, and dispatch layer under `std.nogc_async_mut.kernel_plugin`;
- uses the same typed contracts for static, statically sealed but separately packaged, native dynamic, SMF, worker-process, and optional WebAssembly Component placements;
- generates static registries and product composition images instead of maintaining hand-written registration lists;
- performs every possible check at compile or composition-seal time;
- resolves dynamic identities once and dispatches through dense slots thereafter;
- never passes Simple, Rust, or C++ private AST/object/container layouts across a stable ABI;
- becomes the common kernel for linting, IDE services, compiler providers, and large MDSOC++ programs.

For linting, the design is one **Lint Kernel** with language adapters:

- Simple uses native compiler queries and must include semantic/type/name-resolution diagnostics;
- Rust initially uses `cargo check` / `cargo clippy` JSON in a contained worker, with an exact-toolchain in-process path only as an optional optimization;
- C++ initially uses `clang-tidy` and `clangd`/LibTooling workers driven by `compile_commands.json`, with libclang available for a narrower stable C integration.

For the IDE, the current VS Code extension and Simple editor stack are **valuable foundations but are not yet sufficient for the unified target**. VS Code should remain a thin, capable UI shell. SVIM/Simple IDE should remain the native/minimal/SimpleOS shell. Both should consume the same editor-neutral tooling kernel and language sessions. Heavy analysis must not be duplicated in `extension.ts`, fallback providers, and separate native editor code.

MDSOC++ is defined as:

```text
MDSOC++
  = MDSOC typed boundaries and ownership
  + optional MDSOC+ ECS/data-oriented inner layer
  + sealed kernel-plugin composition
  + bounded no-GC async command/event/query transport
  + capability authority, generations, receipts, and rollback
```

The first implementation critical path is:

```text
freeze reusable contracts
  -> generate and validate one static plugin graph
  -> implement bounded async lifecycle and dense dispatch
  -> migrate Simple lint in shadow mode
  -> add Rust and C++ worker adapters
  -> converge editor ExtensionHost and tooling sessions
  -> adapt compiler providers
  -> publish MDSOC++ product framework
```

---

## 1. Scope and non-goals

### 1.1 Goals

This design must achieve all of the following:

1. Create a reusable kernel-plugin library in the no-GC async family.
2. Preserve and extend the current SCI/provider-query architecture rather than replace it.
3. Improve `simple lint` and converge `simple check` with a trustworthy semantic pipeline.
4. Support linting Simple, Rust, and C++ through one result/configuration/scheduling model.
5. Apply the same library to the Simple IDE, SVIM, VS Code integration, and compiler providers.
6. Upgrade MDSOC+ into MDSOC++ for large programs without forcing overhead into hot paths.
7. Detect duplicate IDs, missing providers, invalid dependencies, version mismatch, forbidden dynamic behavior, invalid enum extensions, capability mismatch, and impossible lifecycle combinations as early as possible.
8. Provide an implementation plan designed for many parallel agents with strict ownership and merge ordering.
9. Keep static use close to direct-call cost, and make dynamic overhead local and measurable.
10. Be robust under plugin failure, cancellation, reload, partial tool availability, malformed output, and mixed toolchain versions.

### 1.2 Explicit non-goals

- Do not implement complete Rust or C++ frontends in Simple as the first step.
- Do not clone the whole VS Code Extension API.
- Do not expose native Simple AST/HIR/MIR, Rust HIR/MIR, or Clang AST class layouts as the stable plugin ABI.
- Do not create one shared object/process per lint rule; plugins are coarse providers, while rules remain fine-grained scheduled units inside them.
- Do not compile or repair a missing production plugin at runtime.
- Do not scan the repository, parse SDN, start a worker, or load ordinary plugins for root `--help`/`--version`.
- Do not make runtime-open `dyn:` extensions legal in critical sealed logic merely because the artifact happens to be local.
- Do not require ECS inside every MDSOC++ capsule. ECS remains optional and domain-dependent.
- Do not move kernel/drivers to MDSOC++ automatically; hard-real-time and low-level code may remain MDSOC-only.
- Do not add new language grammar in Phase 1. Typed declarations, existing annotations/macros where available, SDN schema compilation, and the existing extended-enum grammar are sufficient.

---

## 2. Evidence and current repository baseline

### 2.1 Previous compiler-kernel/plugin research recovered

The direct predecessor is:

```text
simple_compiler_kernel_plugin_bootstrap_refactor_plan_2026-08-30.md
SHA-256: 3d0fd1432e0628a4c232d2cd7a77af526457efeabc0d6eca0261de110aa53bbc
```

That plan established the following decisions, which this document adopts rather than reopening:

- a small compiler kernel owns stable IDs, query/dependency runtime, CAS/action cache, provider admission and scheduling, diagnostics transport, immutable codecs, and lightweight observability;
- parser semantics, type inference, trait solving, borrow checking, MIR construction, optimization policy, and backends remain providers rather than kernel code;
- native AST/HIR/MIR structures do not cross a stable dynamic boundary;
- static and dynamic placement use one logical provider contract;
- provider artifacts are digest locked, atomically published, generation pinned, and never unloaded before quiescence;
- configuration is inert data and cannot execute or compile code;
- `adhoc`, normal incremental, and full bootstrap flows remain explicit;
- shadow execution, optional cutover, and rollback precede deletion of old paths;
- generated registries replace central files importing every backend;
- typed receipts explain reuse, rebuild, load, test selection, and admission decisions;
- parallel agents do not independently edit shared V1 wire layouts or generated registries.

This new plan is a focused successor. It generalizes the provider design into reusable software and applies it to linting, IDE/tooling, and MDSOC++.

### 2.2 Current composition/provider implementation

The accepted current direction is already `simple-core + SimpleCompositionImageV1 + providers`. The repository has a substantial synchronous no-GC composition library under:

```text
src/lib/nogc_sync_mut/composition/
```

It includes SCI codecs/source parsing, ABI digests, CLI provider wire types, route/help generation, provider contracts, and registries. The current provider contract is deliberately fixed-width and avoids `text`, `any`, Simple object layouts, language collections, or function values at the stable boundary. `SimpleProviderQueryV1` includes interface/version/host/capability fields, and its result carries a provider context, identity/implementation/ABI digests, and an opaque interface handle.

The dynamic loader already implements several important safeguards:

- approved artifact path classes;
- artifact existence and SHA-256 digest verification;
- capability-bit subset validation;
- host-ABI and interface-version checks;
- process-callable symbol validation;
- retained loader sessions;
- pins that prevent close while an interface is live.

These are the right primitives, but the current implementation is not yet the reusable async kernel:

- loader/session state uses growable arrays and linear pin lookup/removal;
- the loader owns `text`-heavy policy records rather than a compact prevalidated projection;
- lifecycle is not integrated with cancellation, bounded work queues, draining, health checks, or atomic multi-provider generation publication;
- the current `DynSmfSession` still contains hard-coded default manifests/source mappings and can construct background compile commands, which belongs in build/composition tooling rather than runtime loading;
- CLI invocation has a concrete bridge, but a general command/query/event/async operation contract has not yet converged.

### 2.3 Current no-GC async implementation

The repository has useful async building blocks under:

```text
src/lib/nogc_async_mut/async/
```

including futures, polling, cancellation, executor/runtime, combinators, I/O, scheduling, and promises. However, the current general executor/runtime is not yet suitable as the strict kernel-plugin hot path:

- task and ready queues use growable arrays;
- the runtime uses dictionaries for task membership/results;
- one executor finds tasks by linear scan;
- timer handling is linear;
- global task IDs and global runtime state are used;
- cancellation tokens use growable module-global arrays and explicitly note that IDs are not released/reused yet;
- the executor comments acknowledge that opaque runtime polling was removed and pending futures remain an external responsibility.

Therefore the plugin kernel should reuse useful concepts and adapters from this library, but introduce a small bounded substrate with generational slots and preallocated rings. “No-GC async first” means no collector, explicit ownership, bounded state, and an allocation-free sealed run phase—not merely placing an unbounded registry in the `nogc_async_mut` directory.

### 2.4 Current editor extension host

The active Simple editor extension system is under:

```text
src/lib/editor/extensions/
```

It already provides:

- typed extension IDs, semantic versions and ranges;
- SDN manifests with host placement and default-deny permission fields;
- activation events such as `onLanguage:` and `onCommand:`;
- command/event/language registries;
- disposables and per-extension lifetime ownership;
- deactivation cleanup;
- crash-loop containment;
- keybinding, custom editor, theme, and debug-adapter contributions;
- in-process typed activation hooks and command handlers.

The campaign record also identifies current gaps:

- a worker host and external entrypoint execution are not complete;
- handlers are still registered eagerly even though execution is activation gated;
- VS Code capability generation had been disconnected and required repair;
- the editor host is structurally separate from SCI/provider admission, generation pinning, and the compiler provider work.

This system should become an adapter/client of the common Kernel Plugin Library. Its editor contribution model remains useful and must not be discarded.

### 2.5 Current lint implementation

The current Simple lint tool has a large implementation under:

```text
src/compiler/90.tools/lint/
```

It has many useful rules, profiles, diagnostics, fixes, traceability checks, OS/freestanding checks, and naming rules. The architectural problem is ownership and duplication:

- one large Simple-specific model owns profiles, rule names, default levels, configuration, dispatch, diagnostics, and fixes;
- the list of known rule names and the default-level table are hand maintained;
- rule scheduling is not explicitly based on required semantic facts;
- the Rust seed has a second lint framework and diagnostic model;
- there is no C++ adapter;
- CLI/check/lint/LSP reporting do not share one receipt/verdict model.

Two current correctness gaps make convergence urgent:

1. `simple check` is parse-only in its worker path and can return success for type errors and unresolved names. Even the existing driver check entry currently fails to surface these diagnostics by default because semantic enforcement is advisory and its promoted path has an interpreter resolution failure.
2. A warning-only lint result can print a count of warnings and then still print `Lint passed: all files clean` because success text is tied to failed/not-linted file counts rather than the actual verdict.

A trustworthy lint architecture must treat semantic coverage and analysis completeness as first-class output, not infer them from an exit code.

### 2.6 Current VS Code and native Simple IDE state

The current VS Code extension is already feature-rich for a version `0.1.0` shell:

- Simple language registration and TextMate grammar;
- custom rich source editor;
- LSP compatibility surface and restart/output commands;
- fallback diagnostics, semantic tokens, symbols, references, definitions, hover, and folding;
- test controller, CodeLens, test workspace, and editor markers;
- math rendering/sync panels;
- AI commands and UI;
- crash-contained `safeRegister` calls.

However, `extension.ts` is still a large manually wired activation root. It constructs many providers, registers feature groups one by one, and keeps fallback analysis in TypeScript. That is appropriate as a bootstrap shell but not as the long-term source of language truth.

The native editor direction is also valuable:

- SVIM owns editing/session truth in a shared core;
- shell adapters own rendering and input only;
- language tooling is intended to publish diagnostics/decorations through ports;
- a unified editor backend already defines a trait, operation-based undo/redo, syntax facade, project navigator, configuration, and TUI/VS Code adapter stubs.

Its language-service bridge remains deferred, and the VS Code adapter is still a stub rather than a full shared-session integration.

### 2.7 Is the current IDE enough?

| Area | Current state | Enough for the proposed target? | Required action |
|---|---|---:|---|
| Buffer/window/tab/undo core | strong native foundation | yes | retain as editor authority |
| VS Code user-facing feature breadth | strong prototype | yes for shell | preserve and thin |
| LSP client/server seam | present but compatibility/fallback oriented | partial | make common tooling service authoritative |
| Editor extension manifests/activation | useful and tested | partial | adapt to shared kernel-plugin contracts |
| Worker/external extension execution | incomplete | no | implement through common worker transport |
| Shared Simple/Rust/C++ analysis session | absent | no | add language-provider sessions |
| Compile/seal-time plugin graph validation | absent in editor host | no | generate from typed declarations/SCI |
| No-GC async bounded runtime | absent | no | implement kernel substrate |
| Common CLI/LSP/SARIF diagnostic truth | absent | no | add diagnostic/fix/receipt wire model |
| Static/direct fast path | not generalized | no | generated dispatch and specialization |
| Native and VS Code feature parity | partially represented by stubs/generation | no | capability matrix and protocol tests |

**Conclusion:** there is enough implementation to avoid a rewrite, but not enough architectural convergence to call the IDE complete. The right strategy is preservation plus extraction, not replacement.

---

## 3. External architecture research and implications

### 3.1 VS Code

VS Code separates static manifest contribution points, lazy activation events, and runtime API registration. It may run extensions in local, browser, or remote extension hosts, and its host exists specifically to contain startup/performance/stability impact. Language servers split a lightweight editor client from a potentially heavy analysis server in another process and make one language service reusable across editors.

**Implications for Simple:**

- keep static UI contributions declarative and generated;
- activate only by selected language/command/workspace need;
- keep CPU/memory-heavy analysis outside the UI shell;
- distinguish UI placement from workspace/data placement;
- use LSP for standard editor features and a small typed extension protocol only for Simple-specific capabilities.

### 3.2 Rust, Clippy, Cargo, and rust-analyzer

Clippy distinguishes early lint passes that need syntax/AST information from late passes that need types and symbol information. It uses exact-output UI tests and explicit lint registration/documentation. Cargo and rustc provide structured JSON diagnostic streams. `rustc_public` is moving toward a public compiler-analysis API, but its own documentation still describes an evolving goal and currently requires queries within compiler callbacks. rust-analyzer is a reusable LSP IDE backend.

**Implications for Simple:**

- model rule requirements explicitly rather than letting every rule receive every compiler object;
- use Cargo/rustc JSON as the stable first integration boundary;
- use rust-analyzer as the initial IDE backend instead of rebuilding Rust IDE semantics;
- keep direct `rustc_driver`, Clippy internals, or `rustc_public` access in an exact-toolchain worker/provider until stability is sufficient;
- preserve Rust fix spans/applicability and test them through the common fix model.

### 3.3 Clang, clang-tidy, clangd, and LLVM

Clang documents three distinct integration levels:

- libclang: narrower, stable high-level C interface;
- Clang plugins/LibTooling: full AST control but toolchain-version coupling;
- clang-tidy: modular lint/check framework built on LibTooling.

C++ semantic tools require the actual compile command for each translation unit; the JSON compilation database exists to replay those invocations independently of the build system. clangd combines compiler and clang-tidy diagnostics with fixes and uses responsiveness heuristics rather than regenerating every diagnostic after every keystroke. LLVM’s pass managers separate analysis from transformation and model preserved/invalidated analyses.

**Implications for Simple:**

- `compile_commands.json` or an equivalent captured build projection is mandatory evidence; fallback flags must produce an incomplete receipt, not a false clean result;
- use clang-tidy/clangd workers first;
- use libclang only where its stable surface is sufficient;
- keep full LibTooling/Clang AST checks behind a version-pinned worker or same-build provider;
- carry analysis invalidation/preservation into the common fact-cache model.

### 3.4 WebAssembly Component Model and WIT

WIT defines language-independent interfaces and worlds; the Canonical ABI defines cross-language representation. Components communicate through typed imports/exports rather than sharing private object memory. WASI 0.3, ratified in June 2026, adds native component-model async primitives such as async functions, streams, and futures.

**Implications for Simple:**

- the Simple fixed-width native ABI remains the lowest-overhead trusted path;
- WIT generation is a strong optional portable/sandboxed plugin path;
- WIT should be generated from the same canonical interface schema, not authored as a second truth;
- WebAssembly is suitable for untrusted/community rules and portable tools, but should not be forced into every trusted static hot path.

### 3.5 LSP and SARIF

LSP standardizes editor-facing document/diagnostic/code-action interactions without trying to standardize every language’s AST. SARIF 2.1.0 standardizes static-analysis result interchange.

**Implications for Simple:**

- keep the internal fact/query protocol richer and editor-neutral;
- adapt it outward to LSP diagnostics/code actions;
- export the same normalized results to SARIF for CI/code-host integration;
- never parse human-readable compiler output when structured output exists.

### 3.6 Comparative architecture table

| Pattern | Startup/hot-path cost | Isolation | ABI stability | Compile-time checking | Best Simple use |
|---|---:|---:|---:|---:|---|
| Generated static direct call | minimum; inlineable | process trust only | source/schema controlled | maximum | kernel-critical built-ins and hot providers |
| Generated static table | one indirect call | process trust only | exact-build or stable table | high | selectable built-in families |
| Native/SMF dynamic provider | resolve once, then indirect call | weak process isolation | stable C/fixed-wire boundary | seal + load checks | signed trusted optional providers |
| Worker process | IPC/batching cost | strong crash/memory isolation | protocol/versioned wire | schema + handshake | Rust/C++ toolchains, vendor tools, unstable APIs |
| Language server | IPC plus incremental service | strong UI isolation | standardized editor protocol | protocol/schema | IDE language features |
| WebAssembly Component | canonical-lift/lower cost | sandbox/capabilities | WIT/Canonical ABI | component linking | untrusted or portable third-party plugins |
| Compiler-internal plugin | low within same compiler | little isolation | toolchain-coupled | compiler types | optional exact-toolchain experiments only |

No single placement wins every case. The reusable kernel must make placement a policy choice behind one logical contract.

---

## 4. Core architecture principles

### 4.1 One composition authority

`SimpleCompositionImageV1` and its successors remain the runtime’s immutable composition authority. Runtime code does not merge text manifests, guess providers, inspect source, or run a compiler.

### 4.2 One provider discovery boundary

`SimpleProviderQueryV1` remains the canonical native/SMF discovery entry. New plugin interfaces are queried by interface ID and version rather than adding an unrelated loader protocol.

### 4.3 Closure is not placement

Two independent axes must never be collapsed:

```text
closure:   static | complete | dyn
placement: erased | static-direct | static-table | native | smf | worker | wasm
```

Examples:

- a `complete` provider graph may be packaged as native libraries but sealed before launch;
- a `dyn` plugin may be in-process but is still semantically runtime-open;
- a `static` provider may be erased entirely for a product that does not select it.

### 4.4 Stable boundary, private internals

The stable boundary contains:

- fixed-width integers/flags;
- offsets and lengths into caller/host-owned byte arenas;
- versioned descriptors;
- opaque handles with explicit release;
- stable IDs and digests;
- no private language collections or object graphs.

Provider-private native structures remain behind the provider boundary.

### 4.5 Static first, dynamic by policy

The same plugin implementation may have multiple generated placements. Product-critical and hot paths default to static direct or static table. Native/worker/Wasm placements are chosen for optionality, isolation, toolchain coupling, or trust reasons—not because every plugin must be dynamic.

### 4.6 Bounded no-GC run phase

Allocation may occur during composition compilation, process startup, provider admission, or explicitly configured dynamic expansion. A sealed strict run phase must be able to operate with:

- preallocated registries;
- generational slot maps;
- bounded request/completion/event rings;
- fixed diagnostic arenas or bounded chunks;
- no collector and no hidden per-dispatch heap allocation;
- explicit overload/backpressure status.

### 4.7 Coarse physical providers, fine logical rules/queries

A plugin binary/process is a deployment and trust boundary. A lint rule, compiler query, editor command, or optimization pass is a scheduling unit. Do not create hundreds of physical plugins to achieve fine invalidation.

### 4.8 Fail closed without false green

Unknown required capability, missing semantic fact, malformed tool output, unavailable compile command, skipped file, plugin crash, timeout, or zero analyzed input must be represented explicitly. None may become “clean.”

### 4.9 Generated truth

Provider catalogs, rule catalogs, command contributions, enum extension tables, default lint levels, interface bindings, C/Rust/C++ headers, WIT, documentation indexes, and static registries are generated from one typed declaration graph.

### 4.10 Receipts over hidden behavior

Every run records:

- selected composition and generation;
- requested/provided interfaces;
- files/rules/facts planned and actually processed;
- cache reuse and invalidation reasons;
- skipped/incomplete work;
- diagnostics/fixes counts;
- toolchain/build configuration identity;
- timing and bounded resource counters.

---

## 5. Target architecture

```text
                               build/configuration time

 typed plugin declarations + rule declarations + product SDN + schemas
                                |
                                v
                    simple-configc / plugin-gen
                     |         |          |
                     |         |          +--> C / Rust / C++ / WIT bindings
                     |         +-------------> generated static registries
                     +-----------------------> immutable SCI projections

                                 runtime

 +-----------------------------------------------------------------------+
 | Product kernel / MDSOC++ kernel                                       |
 |                                                                       |
 |  SCI reader -> admission -> sealed graph -> generation publication    |
 |       |             |             |                 |                  |
 |       |             |             |                 +-> rollback       |
 |       |             |             +-> dense slots / direct bindings   |
 |       |             +-> capability leases / digests / ABI checks      |
 |       +-> route/activation index                                      |
 |                                                                       |
 |  bounded async substrate                                               |
 |  task slots | request ring | completion ring | event ring | timers     |
 |  cancellation | deadlines | backpressure | quiescence | receipts      |
 +--------------------------+--------------------------------------------+
                            |
          +-----------------+------------------+------------------+
          |                                    |                  |
  static/direct providers              native/SMF providers     workers/Wasm
          |                                    |                  |
          +----------------- typed interface operations ---------+
                            |
             +--------------+------------------------------+
             |              |              |               |
          lint kernel   tooling/IDE     compiler        application
          providers     providers       providers       MDSOC++ plugins
```

The library is reusable because product-specific concepts—lint rules, editor commands, compiler queries, database tasks—are interfaces above a common composition/lifecycle/dispatch kernel.

---

## 6. Kernel Plugin Library design

### 6.1 Repository placement

Keep stable composition/wire fundamentals where they already live and add an async layer:

```text
src/lib/nogc_sync_mut/composition/          # existing canonical SCI/wire core
    provider_contract.spl
    abi_digest.spl
    codec.spl
    source.spl
    ...

src/lib/nogc_async_mut/kernel_plugin/
    __init__.spl
    contract_facade.spl                     # re-export, do not fork sync contracts
    ids.spl
    closure_and_placement.spl
    capabilities.spl
    declaration.spl
    graph.spl
    seal.spl
    static_registry.spl                     # generated facade
    dense_index.spl
    slot_map.spl
    ring.spl
    scheduler.spl
    cancellation.spl
    deadline.spl
    lifecycle.spl
    generation.spl
    dispatch.spl
    host_services.spl
    diagnostics_wire.spl
    text_edit_wire.spl
    receipt_wire.spl
    health.spl
    error.spl
    transport/
        static_direct.spl
        static_table.spl
        native_provider.spl
        smf_provider.spl
        worker.spl
        wasm_component.spl                  # optional after worker path
    testing/
        fake_provider.spl
        fault_provider.spl
        deterministic_scheduler.spl
```

The async library imports `std.nogc_sync_mut.composition`; the reverse dependency is forbidden.

### 6.2 Public module families

| Module family | Responsibility | Allowed allocation during sealed run? |
|---|---|---:|
| `contract` | stable IDs, versions, descriptors, operation/request/result wire | no |
| `compose` | graph construction, validation, capacity calculation, SCI projection | not used in sealed run |
| `runtime` | slots, rings, lifecycle, generations, cancellation, deadlines | no in bounded profile |
| `transport` | static/native/SMF/worker/Wasm adaptation | placement-dependent; bounded by contract |
| `tooling` | normalized diagnostics, edits, progress, receipts | bounded arenas/batches |
| `testing` | fault injection, deterministic scheduling, mutation/non-vacuity | test-only |

### 6.3 Stable identity

Use a canonical persistent identity independent of load order:

```text
PluginId       = namespace/name digest + canonical text in build metadata
InterfaceId    = stable 64/128-bit schema identity
OperationId    = interface-local stable ordinal or digest
RuleId         = language/provider/rule persistent identity
GenerationId   = monotonic process-local generation
SlotHandle     = {index, generation}
RequestId      = {runtime instance, sequence}
```

Rules:

- dense runtime indices are never serialized;
- plugin load order cannot define identity;
- renamed IDs require an explicit compatibility alias;
- aliases are acyclic and expire by declared product version;
- a provider-qualified extended-enum case derives its persistent identity from owner enum, provider ID, local case, and payload schema ABI;
- every externally visible ID has one canonical textual form for diagnostics and one compact form for execution.

### 6.4 Version axes

Do not use one version number for everything.

| Axis | Example | Compatibility rule |
|---|---|---|
| kernel runtime ABI | `KernelPluginRuntimeV1` | major exact; minor provider >= request |
| provider query ABI | existing `SimpleProviderQueryV1` | retain V1 compatibility |
| interface schema | `LintProviderV1` | schema major exact; additive minor |
| wire record | `DiagnosticV1` | `descriptor_size` + versioned fields |
| plugin implementation | provider semver/build digest | product policy |
| product composition | SCI digest/version | exact admitted image |
| toolchain identity | rustc/Clang/Simple compiler | cache and compatibility input |
| payload schema | enum/command/query payload | explicit ABI digest |

A plugin implementation update with unchanged interface/schema need not rebuild the kernel. A schema-major change requires adapters or consumer rebuilds, not silent reinterpretation.

### 6.5 Closure and placement types

No new grammar is required initially:

```simple
enum PluginClosure:
    Static
    Complete
    Dyn

enum PluginPlacement:
    Erased
    StaticDirect
    StaticTable
    NativeDynamic
    SmfDynamic
    Worker
    WasmComponent

enum PluginCriticality:
    Critical
    Robust
    Normal
    Experimental
```

Validation examples:

- `Critical + Dyn` is rejected.
- `Critical + Worker` requires startup admission, bounded transport, restart policy disabled or explicitly verified, and no runtime-open dependency.
- `Complete + NativeDynamic` is valid when the exact artifact/digest is sealed into SCI.
- `Static + Erased` is valid for an unselected product feature.
- `WasmComponent` requires generated WIT and declared canonical-ABI version.
- an operation declared `noalloc_run` cannot route to an adapter that allocates per request.

### 6.6 Typed declarations, not a second manifest language

Phase 1 should use typed Simple declarations or schema-validated SDN compiled by `simple-configc`. Example pseudocode:

```simple
const SIMPLE_SEMANTIC_LINT = PluginDeclV1(
    id: plugin_id("simple.lint.semantic"),
    version: semver("1.0.0"),
    closure: PluginClosure.Complete,
    preferred_placement: PluginPlacement.StaticDirect,
    provides: [lint_provider_v1("simple")],
    requires: [source_snapshot_v1(), simple_semantic_query_v1()],
    capabilities: [WorkspaceRead, DiagnosticPublish],
    run_policy: RunPolicy.NoAllocAfterSeal,
    capacities: PluginCapacityDecl(...)
)
```

The declaration compiler emits:

- SCI provider/interface records;
- a static direct/table registry;
- native C ABI bindings;
- Rust/C++ SDK bindings;
- optional WIT;
- documentation and rule catalogs;
- graph/capacity evidence.

An optional `@plugin` annotation may be added later only if it materially improves ergonomics. It is not a prerequisite.

### 6.7 General operation ABI

Retain `SimpleProviderQueryV1`. Add a queried general runtime interface rather than adding many unrelated discovery symbols.

Conceptual wire records:

```simple
struct KernelOperationRequestV1:
    descriptor_size: u32
    request_id_hi: u64
    request_id_lo: u64
    operation_id: u64
    input_offset: u32
    input_length: u32
    output_capacity: u32
    deadline_ns: u64
    cancellation_handle: u64
    flags: u64

struct KernelOperationResultV1:
    descriptor_size: u32
    status: i32
    state: u32                 # ready, pending, backpressure, cancelled, failed
    output_offset: u32
    output_length: u32
    diagnostic_offset: u32
    diagnostic_length: u32
    continuation_handle: u64
```

Canonical dynamic symbols may be:

```c
int32_t simple_provider_query_v1(const QueryV1*, QueryResultV1*);
int32_t simple_provider_invoke_v1(uint64_t interface_handle,
                                  uint64_t provider_context,
                                  const OperationRequestV1*,
                                  OperationResultV1*);
int32_t simple_provider_poll_v1(...);
int32_t simple_provider_cancel_v1(...);
int32_t simple_provider_release_v1(...);
```

Rules:

- no language-native future crosses the boundary;
- no callback captures host memory without an explicit lease;
- output buffers are caller-owned or provider-owned behind an explicit release handle;
- the host validates all offsets/lengths before reading;
- native tables/pointers are an optional exact-build fast path, never the only correctness path;
- static-direct generation bypasses the wire encode/decode when both sides are compiled together, while parity tests ensure equivalent semantics.

### 6.8 Bounded async substrate

The kernel runtime needs purpose-built structures:

```text
GenerationalSlotMap<PluginState>
GenerationalSlotMap<RequestState>
BoundedMpscRing<RequestEnvelope>
BoundedMpscRing<CompletionEnvelope>
BoundedRing<EventEnvelope>
TimerWheel / bounded deadline heap
FixedArena or chunk pool for payload/diagnostic bytes
GenerationPinTable
```

Profiles:

| Profile | Allocation policy | Intended use |
|---|---|---|
| `NogcDynamic` | explicit allocator allowed; never GC | desktop development/default migration |
| `NogcBounded` | allocate during create/prepare; no allocation after seal | IDE daemon, server, embedded robust mode |
| `NogcStatic` | capacities compile-time/static; no runtime heap | firmware/critical fixed products |

Required behavior:

- every enqueue can return `Accepted`, `Coalesced`, `Backpressure`, or `Rejected`;
- cancellation is generational so stale token IDs cannot cancel a reused slot;
- deadline expiry is handled by the kernel, not separately by each provider;
- document-change and diagnostic events may coalesce by key/version;
- provider callbacks cannot recursively monopolize the scheduler; per-turn work budgets apply;
- completion ordering is deterministic where the interface promises determinism;
- detached task results are explicitly dropped, not retained in an unreachable map;
- all slot/arena/ring high-water marks are observable.

### 6.9 Lifecycle state machine

```text
Declared
  -> Indexed
  -> Admitted
  -> Prepared
  -> Starting
  -> ShadowActive
  -> Published
  -> Draining
  -> Retired
  -> Unloaded

Any active state -> Faulted -> Disabled | RestartPending | RolledBack
```

Transition rules:

1. **Index:** read only validated SCI projections; do not execute plugin code.
2. **Admit:** verify path, artifact digest/signature, ABI/schema, target, capability ceiling, and placement.
3. **Prepare:** allocate bounded resources, construct capability leases, resolve required interfaces, and run non-executing validation.
4. **Start:** invoke lifecycle start under timeout/cancellation.
5. **Shadow:** run health/parity probes without routing production traffic.
6. **Publish:** atomically swap a whole compatible generation, not individual inconsistent entries.
7. **Drain:** reject new requests, cancel or finish in-flight work by policy, detach listeners.
8. **Retire:** keep code/resources while pins remain.
9. **Unload:** only after zero requests, zero pins, zero callbacks, zero borrowed buffers, and quiescence.

The prior generation remains selectable until the new one passes publication gates.

### 6.10 Capabilities as leases

The current editor permission booleans can map into a richer common authority model. A boolean states policy; an actual host operation requires a capability-scoped handle/lease.

Example capabilities:

```text
workspace.read
workspace.edit
filesystem.read:<root>
filesystem.write:<root>
network.connect:<policy>
process.spawn:<toolchain-id>
ui.command
ui.view
language.snapshot
language.semantic-query
compiler.internal-query
persistent-state:<namespace>
clock.monotonic
entropy
native.unsafe
```

Rules:

- requirements are declared and checked as a subset at seal time;
- concrete resource scopes are checked at admission;
- providers receive only handles for granted services;
- a dynamic aspect/plugin cannot expand the target provider’s authority;
- worker and Wasm transports receive serialized capability handles, not ambient OS access;
- capability use is included in receipts and audit events;
- critical profiles reject wildcard roots/hosts/tools.

### 6.11 Host services

Kernel-owned host interfaces should be small and versioned:

- allocator/arena access;
- source snapshot and content hash;
- cancellation/deadline polling;
- diagnostic/fix publication;
- structured logging and tracing;
- immutable config lookup;
- command/event/query dispatch;
- workspace/file access through capabilities;
- process/toolchain execution through a worker supervisor;
- cache/CAS access with provider and schema namespaces;
- monotonic clock;
- health and receipt emission.

A provider cannot import an arbitrary product singleton. This is the main mechanism that keeps MDSOC++ capsules testable and prevents hidden dependency graphs.

### 6.12 Static dispatch and overhead minimization

#### Static-direct

Generated code binds a required interface to one provider function. The compiler may inline and eliminate wrapper records. There is no registry lookup in the hot path.

#### Static-table

The composition generator assigns a dense slot and emits an array/function table. Dispatch is one bounds check plus one indirect call. If the selected set has one provider, specialization may collapse it to direct.

#### Native/SMF dynamic

String/digest/version lookup happens during admission only. The result is stored in a dense generation slot. A normal call performs:

```text
validate generational slot -> load target/context -> one indirect call
```

No hash lookup, semver parsing, manifest parsing, or filesystem check occurs per call.

#### Worker

Requests are batched into a bounded ring or framed stream. Small editor changes coalesce. Diagnostic arrays and edits are returned in batches. A worker is selected when isolation and toolchain compatibility outweigh call overhead.

#### Wasm

WIT/canonical ABI lift/lower is accepted as the isolation/portability cost. Wasm is not used for the compiler’s hottest trusted built-in path by default.

### 6.13 Compile-time, seal-time, load-time, and runtime checks

| Check | Earliest required phase |
|---|---|
| malformed typed declaration/schema | compile time |
| duplicate plugin/interface/rule/command ID | compile time |
| duplicate provider-qualified enum case | compile time |
| static dependency cycle | compile time |
| missing required static provider | compile time |
| interface major/minor incompatibility in selected product | seal time |
| forbidden `dyn` dependency in critical graph | seal time |
| capability requirement exceeds product ceiling | seal time |
| invalid placement for noalloc/critical/threading policy | seal time |
| capacity calculation exceeds declared product budget | seal time |
| unknown complete-enum extension or non-exhaustive match | seal time/link time |
| artifact digest/signature/target mismatch | load time |
| process-callable symbol/worker handshake mismatch | load time |
| stale generational handle | runtime, typed failure |
| backpressure/deadline/cancellation | runtime, typed status |
| provider crash/malformed response | runtime containment |

The compiler should emit concrete dependency traces, not only “plugin invalid.”

### 6.14 Security and fault containment

- manifests and SCI are inert; no plugin code runs during decoding;
- only declared artifacts and exact digests are admitted;
- native providers default to signed/trusted products;
- third-party/untrusted providers default to worker or Wasm placement;
- worker process privileges and filesystem roots derive from capability leases;
- every dynamic response is bounds/schema validated;
- crash-loop state is generation scoped;
- repeated failure disables only the provider/generation, not the whole host;
- activation is transactional and rollback is atomic;
- event listeners, commands, timers, buffers, and callbacks are lifetime owned and disposed on drain;
- no unload occurs while executable addresses may still be referenced;
- configuration cannot raise a capability ceiling established by the product image;
- no runtime fallback silently selects an ABI-incompatible provider.

---

## 7. Extended enums as the plugin semantic extension mechanism

### 7.1 Current capability

Simple’s current enum-extension grammar already supports the necessary semantic distinction:

```simple
enum ExprKind:
    Int(v: i64)
    complete:
    dyn:

extend ExprKind:
    complete:
        async.Await(v: i64)
        gpu.KernelLaunch(k: i64)
    dyn:
        ide.LiveProbe(p: i64)
```

The current tests also require provider-qualified dotted constructors and distinguish `case complete ext:` from `case dyn ext:`. This is a strong basis for plugin-aware closed-at-seal and runtime-open variants.

### 7.2 Required interpretation

| Enum region | Closure point | Dispatch representation | Critical use |
|---|---|---|---|
| ordinary cases | defining module compile | native dense tag | allowed |
| `complete:` extension cases | product composition seal | generated dense extension tag/table | allowed after proof |
| `dyn:` extension cases | runtime | persistent qualified identity resolved to dynamic slot | rejected in critical exhaustive logic |

A complete extension is not “dynamic.” It is an extension supplied outside the original enum definition but included in a finite product closure before publication.

### 7.3 Persistent identity

For each extension case, persist:

```text
(owner enum SymbolId,
 provider PluginId,
 provider-local case ordinal/name,
 payload schema ABI version/digest)
```

After product sealing, generate a dense process tag for speed. Never store that dense tag in files, caches, RPC, or diagnostics.

### 7.4 Where extended enums should be used

Good uses:

- plugin interface/contribution kinds with semantic pattern matching;
- compiler IR extension nodes where a product seals all complete providers;
- editor contribution kinds that products may extend;
- MDSOC++ command/event/query variants with product-sealed cases;
- backend or target-specific typed operations.

Poor uses:

- arbitrary diagnostic IDs, where stable integer/string IDs plus metadata are simpler;
- every lint rule, where a generated rule table is better than a huge match;
- untrusted payloads before schema validation;
- values whose only operation is lookup/forwarding.

### 7.5 Plugin-oriented example

```simple
enum ToolingRequest:
    OpenDocument(uri: text)
    CloseDocument(uri: text)
    complete:
    dyn:

extend ToolingRequest:
    complete:
        simple.SemanticLint(document: DocumentHandle)
        rust.ClippyWorkspace(workspace: WorkspaceHandle)
        cpp.ClangTidyTranslationUnit(unit: TranslationUnitHandle)
    dyn:
        experiment.CustomAnalysis(payload: ByteSlice)
```

Critical server code can match every built-in and complete case after seal. Runtime-open experimental cases must route through a generic validated dynamic handler and cannot enter a critical exhaustive branch.

### 7.6 Compiler work required

1. Make the product composition/seal phase the authority that freezes `complete:` cases.
2. Generate persistent-ID-to-dense-tag tables.
3. Reject duplicate provider/case/payload identities.
4. Include extension set and payload schema digests in cache/action keys.
5. Make exhaustiveness aware of ordinary + selected complete cases.
6. Reject wildcard matching in critical code when a more precise complete-case proof is required.
7. Require `case dyn ext:` or an explicit dynamic policy for runtime-open cases.
8. Generate reflection/binding data for IDE, C, Rust, C++, and WIT.
9. Test extension-order independence.
10. Preserve the current grammar; do not add a competing registration keyword.

---

## 8. Unified Lint Kernel

### 8.1 Architecture

```text
workspace/build inputs
        |
        v
 Language Adapter Session
  Simple | Rust | C++
        |
        v
 normalized facts/query capabilities
 text -> tokens -> syntax -> symbols -> types -> cfg/dataflow -> project/build
        |
        v
 rule planner + incremental cache + bounded async scheduler
        |
        v
 diagnostics + fixes + coverage + receipt
        |
   +----+------------------+----------------+
   |                       |                |
 human CLI              LSP             JSON/SARIF
```

The kernel does not demand one universal AST. Each language adapter exposes named fact/query capabilities and stable handles.

### 8.2 Core contracts

Conceptual public types:

```simple
enum LintFactKind:
    SourceText
    Tokens
    SyntaxTree
    Symbols
    Types
    ControlFlow
    DataFlow
    Effects
    BorrowOwnership
    ProjectGraph
    BuildConfiguration
    complete:
    dyn:

enum LintVerdict:
    Clean
    Warnings
    Errors
    Incomplete
    ToolFailure
    Cancelled
    TimedOut
    NoInput

struct LintRuleDescriptorV1:
    rule_id: RuleId
    language_id: LanguageId
    provider_id: PluginId
    category: CategoryId
    default_level_by_profile_offset: u32
    required_fact_bits: u64
    optional_fact_bits: u64
    fix_kind: u32
    determinism: u32
    rule_schema_version: u32

struct LintRunReceiptV1:
    verdict: LintVerdict
    discovered_files: u32
    planned_files: u32
    analyzed_files: u32
    skipped_files: u32
    selected_rules: u32
    executed_rules: u32
    failed_rules: u32
    error_count: u32
    warning_count: u32
    note_count: u32
    missing_fact_count: u32
    provider_generation: u64
    composition_digest: Digest256
```

### 8.3 Rule declaration and generated catalog

Replace `all_lint_names()`, hand-coded known-name matches, and duplicated default tables with one declaration per rule. The generator emits:

- canonical rule catalog;
- profile defaults;
- aliases/deprecations;
- CLI configuration schema;
- documentation index;
- LSP/SARIF rule metadata;
- Simple/Rust/C++ bindings;
- static provider registration;
- tests proving every declared rule has an implementation and every implementation is declared.

A rule declaration includes:

- stable ID and language;
- summary/rationale/category;
- introduced/deprecated version;
- default levels by profile;
- required facts;
- scope: token/node/function/module/project/workspace/build;
- fix availability and applicability;
- determinism/cacheability;
- cost/resource class;
- critical profile eligibility;
- neighboring/conflicting rules.

### 8.4 Fact-based scheduling

Rules declare facts; they do not call arbitrary frontend internals.

Example:

```text
trailing-whitespace       -> SourceText
naming.function           -> SyntaxTree + Symbols
unresolved-name           -> Symbols
assignment-type-mismatch  -> Types
lock-order-cycle          -> ControlFlow + Effects + ProjectGraph
unsafe-ffi-layout         -> Types + TargetABI + BuildConfiguration
```

The scheduler:

1. determines selected files/rules;
2. computes the minimal required fact closure;
3. asks the language adapter for each fact once per compatible snapshot;
4. runs independent read-only rules in parallel within memory budgets;
5. sorts externally visible output deterministically;
6. records any unavailable fact and affected rules;
7. invalidates only facts/rules affected by a document/build/config/toolchain change.

### 8.5 Simple adapter

The Simple adapter is the first native implementation and should expose:

```text
source snapshot
parse diagnostics and recoverable syntax tree
module surface/import resolution
HIR/type/effect/ownership queries
CFG/dataflow where available
compiler diagnostics
source maps and suggested edits
```

Critical changes:

- connect `check` to a real semantic entry that returns diagnostics, not advisory log text;
- fix the current `TypeInferError` resolution/enforcement path before making semantic check authoritative;
- run a repository-wide violation census before promoting existing advisory checks;
- keep a clearly named `--syntax-only` fast tier if still useful, but never label it a full clean check;
- make `simple check` a preset/client of the same lint kernel rather than a permanently separate parser-only implementation;
- compare Rust seed and self-hosted Simple adapter outputs during migration;
- include exact analyzed fact coverage in every result.

Suggested CLI semantics:

```text
simple check                   # required syntax + name + type/compiler diagnostics
simple check --syntax-only     # explicit reduced coverage; receipt says syntax-only
simple lint                    # configured compiler + lint rules
simple lint --profile critical # semantic coverage required; incomplete is failure
```

### 8.6 Rust adapter

#### Phase 1: contained structured worker

Use:

```text
cargo check / cargo clippy --message-format=json
rustc --error-format=json when directly invoked
rust-analyzer for IDE language features
```

The worker reports:

- exact rustc/cargo/clippy/rust-analyzer version and target;
- Cargo metadata/workspace identity;
- enabled features, profile, target, and relevant flags;
- compiler diagnostics, children, spans, suggestions, applicability;
- analyzed crates/targets and any skipped target;
- process status, timeout, malformed records, and stderr not represented as structured diagnostics.

#### Phase 2: custom deep Rust providers

For rules not expressible through existing Clippy/rust-analyzer output:

- run an exact-toolchain sidecar using Clippy/rustc internals or `rustc_public`;
- declare exact toolchain compatibility in the provider descriptor;
- keep it in a worker by default;
- cache by toolchain commit/version and compiler flags;
- never pass Rust compiler object pointers into the Simple host.

#### Why not embed first

Rust compiler internal APIs and callbacks are toolchain coupled. A worker isolates crashes and version churn while structured JSON provides a useful stable baseline.

### 8.7 C++ adapter

#### Phase 1: clang tool workers

Use:

- `clang-tidy` for batch/project checks and fixes;
- `clangd` for incremental IDE diagnostics and code actions;
- `compile_commands.json` as the translation-unit build authority;
- structured wrapper output normalized to `DiagnosticV1`/`TextEditV1`.

A missing or ambiguous compile command produces `Incomplete`, including the exact translation units affected. Falling back to `clang file.cc` may be allowed for toy/ad-hoc mode, but the receipt must state that it is a fallback configuration.

#### Integration options

| Option | Stability | Power | Recommended role |
|---|---:|---:|---|
| clangd protocol | stable editor-facing process | rich IDE features | default IDE path |
| clang-tidy executable | stable command behavior | modular checks/fixes | default batch lint path |
| libclang C API | comparatively stable | narrower AST access | cross-language embedded helper |
| LibTooling | LLVM-version coupled | full AST/control | version-pinned worker |
| Clang compiler plugin | build/toolchain coupled | build-integrated diagnostics/artifacts | optional exact-build mode |

### 8.8 Diagnostic model

One normalized diagnostic contains:

- stable diagnostic/rule ID;
- provider/language/toolchain origin;
- severity and configured effective level;
- primary location and zero or more related locations;
- message template ID plus rendered message;
- notes/help;
- one or more fix groups;
- snapshot/content hash;
- suppression information;
- determinism/cache identity;
- whether it is compiler, lint, configuration, infrastructure, or incomplete-coverage output.

The human renderer may vary by product. The underlying record must remain identical across CLI, LSP, JSON, and SARIF exports.

### 8.9 Fix model

```simple
enum FixApplicability:
    MachineApplicable
    MaybeIncorrect
    HasPlaceholders
    Unspecified

struct TextEditV1:
    uri_id: u64
    expected_snapshot_digest: Digest256
    start_byte: u64
    end_byte: u64
    replacement_offset: u32
    replacement_length: u32
    applicability: FixApplicability
    conflict_group: u64
```

Rules:

- fixes apply transactionally against expected content hashes;
- overlapping edits from one group are rejected unless explicitly composed;
- cross-provider conflicts are shown, not resolved by nondeterministic order;
- safe fix mode applies only machine-applicable, nonconflicting, idempotence-tested edits;
- the kernel re-analyzes after fixes and records introduced/removed diagnostics;
- IDE code actions and CLI `--fix` use the same edit data.

### 8.10 Verdict semantics

Never derive “clean” from `error_count == 0` alone.

```text
Clean       = complete required coverage, zero warnings/errors at effective levels
Warnings    = complete required coverage, warnings present, no errors
Errors      = one or more analysis/compiler/lint errors
Incomplete  = required file/fact/rule/tool/build configuration was unavailable/skipped
ToolFailure = provider/worker/protocol failed before trustworthy completion
Cancelled   = superseded/user cancellation
TimedOut    = deadline exceeded
NoInput     = selection produced zero analyzable inputs
```

Exit policy is separate from truth:

- default may return 0 for `Warnings`;
- `--deny-warnings` returns nonzero;
- `Incomplete`, `ToolFailure`, and `NoInput` are nonzero in CI/critical profiles;
- the final message states the actual verdict, never “all files clean” when warnings exist.

### 8.11 Configuration and suppressions

- one schema covers workspace, package, directory, file, and source-level overrides;
- precedence is explicit and printed by `lint explain-config`;
- unknown rule IDs are errors in CI/critical mode and warnings in interactive migration mode;
- language-native suppressions map to normalized rule IDs without discarding native semantics;
- toolchain version and configuration digest participate in cache keys;
- profile names may remain `Moderate`, `Strict`, `Robust`, `Critical`, but defaults are generated from rule descriptors.

### 8.12 Incremental cache

Key dimensions:

```text
language adapter version
compiler/toolchain identity
source snapshot digest
build flags/features/target
fact schema version
rule implementation/version/config
provider generation and ABI digest
workspace/project graph digest
```

Cache records include dependency edges and whether an analysis result is complete. An incomplete result is never reused as a clean complete result.

### 8.13 Output adapters

- human text with deterministic grouping;
- compact JSON for programmatic consumers;
- LSP diagnostics/code actions/progress;
- SARIF 2.1.0 for CI/code-host upload;
- optional binary wire for daemon/worker transport;
- `lint explain` and `lint receipt` for planning/invalidation/debugging.

### 8.14 Lint plugin granularity

Recommended physical providers:

```text
lint.simple.frontend
lint.simple.semantic
lint.simple.robustness
lint.simple.architecture
lint.rust.toolchain
lint.rust.custom
lint.cpp.clang
lint.cpp.custom
lint.common.text
lint.common.repository
```

Each may contain many rule descriptors. Fine rule selection remains table-driven and incremental.

---

## 9. IDE and tooling architecture

### 9.1 Product roles

| Product | Long-term role |
|---|---|
| VS Code extension | rich UI shell, standard contribution points, custom rich views/editors, thin language client |
| SVIM/Simple IDE | native/shared editor shell for host, TUI, GUI, and SimpleOS |
| Tooling kernel daemon | authoritative workspaces/documents/snapshots/plugins/analysis/test graph |
| Language providers | Simple native service, rust-analyzer broker, clangd broker, format/test/debug providers |
| CLI | headless client; may embed the same kernel or connect to daemon |

### 9.2 Shared tooling session

```text
ToolingWorkspace
  - composition/generation
  - immutable document snapshots
  - project/build models
  - language adapter sessions
  - diagnostics/fixes cache
  - command/test/debug capability registry
  - cancellation by document version
  - progress and receipts
```

The filesystem is not authoritative for an open modified document. The editor sends versioned snapshots/deltas, and every result identifies the snapshot version/digest it analyzed.

### 9.3 Protocol split

Use standard protocols where they fit:

- LSP: diagnostics, completion, hover, symbols, definitions, references, semantic tokens, code actions, inlay hints, workspace edits;
- DAP: debugging;
- test protocol adapter: test discovery/execution/status;
- small Simple tooling protocol: rich blocks/math, plugin composition inspection, MDSOC++ graph, performance receipts, specialized compiler/verification operations.

Do not expose AST/HIR objects over LSP or the custom protocol. Expose stable handles or editor-level results.

### 9.4 VS Code migration

Current `extension.ts` becomes a thin bootstrap:

1. load generated static contribution metadata;
2. construct host services/output and the tooling client;
3. start/connect only when activation requires it;
4. register generic adapters for diagnostics/tokens/symbols/tests/commands;
5. retain VS Code-specific custom editor, view, webview, and UI code;
6. remove duplicated language analysis after authoritative server parity exists;
7. keep a minimal syntax-only fallback only for server-unavailable degraded mode, and label it degraded.

Generated `package.json` contribution fragments should derive from the same plugin declarations used by Simple IDE. A deterministic generator and mismatch test prevent the previous bridge-disconnection class.

### 9.5 Native Simple IDE/SVIM migration

- retain the shared buffer/window/tab/anchor/undo session as editing authority;
- implement a tooling client adapter against the same protocol as VS Code;
- route diagnostics to anchors/quickfix without direct text mutation;
- use the common command/test/debug contribution registry;
- reuse editor-neutral view models where practical, while keeping rendering shell-specific;
- ensure TUI, host GUI, and SimpleOS shells do not fork edit semantics;
- support in-process static tooling for tiny/embedded products and daemon/worker tooling for desktop products through the same interfaces.

### 9.6 Editor plugin classes

Distinguish:

1. **UI contribution plugin:** commands, menus, views, keybindings, themes, custom editors. Usually shell-local and declarative.
2. **Language/tooling provider:** analysis, formatting, tests, refactors, debug configuration. Usually tooling kernel/worker.
3. **Product feature capsule:** domain state and commands, potentially shared across shells.
4. **Untrusted extension:** worker or Wasm with restricted capabilities.

A single extension package may declare multiple components with different placements. Do not force the UI component and heavy workspace component into one process.

### 9.7 Fallback policy

Fallback must be explicit:

```text
Authoritative: full language provider active for exact snapshot/config
Degraded: syntax/text-only local fallback, clearly labeled
Unavailable: no trustworthy result; retain old diagnostics as stale only if labeled
```

The fallback cannot publish “clean” semantic status.

### 9.8 Multi-language IDE integration

Initial strategy:

- Simple: common native language provider/LSP;
- Rust: rust-analyzer as language provider; Cargo/Clippy worker feeds normalized lint results;
- C++: clangd as language provider; clang-tidy worker feeds batch/project lint;
- common UI merges diagnostics by origin and offers native fixes/code actions;
- project model can host mixed-language workspaces without pretending there is one AST.

### 9.9 IDE acceptance answer

The current VS Code and Simple IDE implementations are sufficient as **shell and editor-core foundations**. They are not sufficient as a shared, robust, low-overhead, multi-language plugin architecture. The missing work is concentrated and reusable: common composition/lifecycle, authoritative tooling sessions, worker placement, generated contributions, and diagnostic/fix/receipt unification.

---

## 10. MDSOC++ design

### 10.1 Definition

Current MDSOC+ is MDSOC outer architecture with an optional ECS business/data layer inside userland services/apps. MDSOC++ adds product-scale plugin composition and lifecycle:

```text
MDSOC++ = MDSOC + optional ECS + Kernel Plugin substrate
```

“++” means the second architectural extension, not C++ implementation.

### 10.2 Product kernel responsibilities

The MDSOC++ kernel owns only cross-cutting mechanisms:

- immutable product composition and typed dependency graph;
- interface resolution and dense dispatch;
- lifecycle/generation/rollback;
- bounded async scheduling, cancellation, deadlines, and backpressure;
- capability authority and host services;
- command/event/query routing;
- configuration projection;
- diagnostics, health, metrics, and receipts;
- persistence/cache namespaces where shared.

It does not own domain business logic, feature state, UI rendering, SQL semantics, compiler semantics, or device-specific policy.

### 10.3 Capsule/plugin responsibilities

A product plugin/capsule owns:

- one coherent feature or layer responsibility;
- its private state and invariants;
- commands it handles;
- queries it answers;
- events it emits/consumes;
- explicit required/provided interfaces;
- optional ECS World and systems;
- migrations for its persistent state;
- health checks and resource budgets.

### 10.4 Dependency rules

1. Plugins import contract packages, not sibling private implementation packages.
2. Required interfaces are declared; the product seal resolves them.
3. Optional dependencies return typed absence/capability states.
4. Direct cycles are compile/seal errors unless represented as asynchronous events with an explicit feedback policy.
5. Commands mutate one authoritative owner; queries are read-only by contract.
6. Events are immutable facts and may be buffered/coalesced by declared policy.
7. Cross-capsule mutable object references are forbidden; use IDs/handles/snapshots.
8. Persistent state schemas are independently versioned from plugin code.
9. Hot-path internal calls inside a capsule are ordinary direct calls; the kernel boundary is coarse.
10. Every dynamic plugin is outside the critical static proof unless explicitly sealed as `complete`.

### 10.5 MDSOC, MDSOC+, and MDSOC++ selection

| Context | Recommended architecture |
|---|---|
| OS kernel, interrupt path, low-level driver | MDSOC only |
| data-oriented userland service/app with fixed composition | MDSOC+ |
| large IDE/compiler/server/enterprise suite with optional features and multiple hosts | MDSOC++ |
| firmware with fixed plugin families and strict capacities | MDSOC++ static/complete subset; no runtime `dyn` |
| tiny tool with one feature | plain modules or MDSOC; do not force framework |

### 10.6 MDSOC++ internal shape

```text
ProductKernel
  |
  +-- FeatureCapsule A
  |     +-- state authority
  |     +-- transforms/systems
  |     +-- optional ECS world
  |     +-- adapters
  |
  +-- FeatureCapsule B
  |
  +-- LayerProvider X
  |
  +-- ShellAdapter(s)

Cross-boundary: typed command / query / event / stream only
```

### 10.7 Example: IDE as MDSOC++

```text
kernel: workspace/session, composition, scheduler, authority, receipts
capsules:
  editor.document
  editor.navigation
  editor.test
  editor.debug
  editor.rich-content
  language.simple
  language.rust
  language.cpp
  ai.assist
shells:
  vscode
  svim-tui
  simple-gui
  simpleos-wm
```

The editor buffer remains one state authority. Language plugins publish diagnostics/edits through contracts. UI shells never own separate analysis truth.

### 10.8 Example: compiler as MDSOC++

```text
kernel: stable IDs, query graph, CAS, provider lifecycle, diagnostics
providers:
  frontend.simple
  semantics.types
  semantics.borrow
  ir.mir
  optimizer.cpu
  backend.cpu
  backend.gpu
  backend.vhdl
  backend.lean
shells:
  CLI
  IDE tooling
  build daemon
```

This is the direct bridge to the recovered 2026-08-30 compiler plan.

### 10.9 Performance rule

MDSOC++ must not turn every function call or ECS entity operation into plugin dispatch. The boundary is at a coarse feature/capsule/provider interface. Static product composition can compile interface calls to direct calls. Dynamic dispatch remains only where selected.

---

## 11. Applying the library to current Simple architecture

### 11.1 Convergence map

| Current system | Keep | Move/generalize | Retire after parity |
|---|---|---|---|
| `nogc_sync_mut.composition` | SCI, codecs, provider query, ABI digest | expose through kernel-plugin facade | duplicate manifest/registry formats |
| `os.smf.provider_loader` | admission evidence and process-callable proof | generational slots, bounded pin table, common lifecycle | linear pin arrays/private lifecycle |
| `DynSmfSession` | SMF transport/build integration knowledge | runtime uses prebuilt SCI; build planner moves to build tool | hardcoded runtime default manifest/path/compiler commands |
| editor `ExtensionHost` | contribution model, activation, permissions, disposables, crash state | become editor adapter over common kernel | separate command/event/lifecycle authority |
| VS Code extension | UI features and shell-specific providers | generated contributions + common tooling client | duplicate semantic fallback as normal path |
| unified editor backend/SVIM | edit/session state authority | common tooling/plugin client | adapter stubs and divergent analysis |
| Simple lint rules | rule logic and profiles | generated descriptors/fact scheduler/common diagnostics | hand-maintained name/default tables |
| Rust seed lint | useful Rust-side implementation | adapter to common wire/result model | duplicate user-facing verdict/config model |
| compiler provider plan | IDs/query/cache/provider boundaries | use common lifecycle/placement/receipts | backend-wide static import factory |

### 11.2 Do not perform a package rename first

Moving existing composition code into a new directory before contracts and tests are stable would create broad churn. First add facades/adapters, prove one pilot, and then decide whether a later source move improves ownership.

### 11.3 Compatibility adapters

Required temporary adapters:

- `ExtensionHostAdapterV1` maps editor manifests/commands/events/lifetimes to kernel interfaces;
- `SimpleCliCommandV1Adapter` maps existing CLI provider operations to general kernel operations;
- `DynSmfTransportAdapter` wraps current loader sessions;
- `LegacyLintAdapter` runs existing Simple lint rules and emits normalized diagnostics;
- `CompilerDriverV1Adapter` exposes the current coarse compiler driver while fine providers migrate;
- `VscodeContributionGeneratorAdapter` generates/validates package contribution fragments.

Every adapter has a deletion gate and a production-caller reachability test.

---

## 12. Proposed repository structure after the first complete migration

```text
src/lib/nogc_async_mut/kernel_plugin/
    ... common library ...

src/lib/tooling_kernel/
    contract/
    workspace/
    document/
    protocol/
    lsp/
    dap/
    test_protocol/
    plugin_adapter/

src/compiler/90.tools/lint/kernel/
    catalog/
    planner/
    scheduler/
    diagnostics/
    fixes/
    receipt/
    output/
    adapters/
        simple/
        rust/
        cpp/

src/lib/editor/extensions/
    manifest/                           # editor contribution schema
    kernel_adapter.spl
    vscode_projection.spl
    simple_ide_projection.spl

src/app/toolingd/
    main.spl
    transport_stdio.spl
    transport_socket.spl

src/app/vscode_extension/
    generated/
    src/client/
    src/ui/
    src/fallback/

src/app/svim/
    core/
    tooling_client/
    shells/

src/compiler/kernel_plugin_adapter/
    driver_v1.spl
    query_provider.spl
    backend_provider.spl

src/lib/mdsocpp/
    __init__.spl
    product_kernel.spl
    capsule.spl
    command.spl
    query.spl
    event.spl
    state_migration.spl
    test_harness.spl
```

`src/lib/mdsocpp` should mostly compose/re-export the kernel-plugin primitives with MDSOC-specific ownership rules. It must not duplicate the runtime.

---

## 13. Detailed implementation phases

### Phase 0 — Freeze evidence and non-vacuity gates

**Purpose:** prevent parallel work from building on stale, conflicted, or unwired files.

Changes:

- record exact repository and toolchain SHAs;
- scan all authoritative source/architecture/generated files for conflict markers;
- capture current lint/check/IDE/provider behavior with real negative fixtures;
- add “planned vs actual” counts to test/lint probes;
- establish startup, allocation, dispatch, and memory baselines;
- mark the 2026-08-30 plan and this document as architecture inputs.

Gate:

- a deliberately broken Simple type/name fixture is not reported clean by the new shadow lane;
- a warning-only lint run cannot render `Clean`;
- zero selected/analyzed files cannot render `Clean`;
- every architecture-owned source path is conflict-marker clean;
- test harness demonstrates that removing a registration makes a test fail.

### Phase 1 — Common contract and generated declaration graph

**Purpose:** freeze one reusable V1 contract.

Changes:

- add kernel-plugin facade over existing composition/provider contracts;
- define IDs, closure, placement, criticality, lifecycle, operation, diagnostic, edit, and receipt schemas;
- implement typed declaration/schema compiler;
- generate static registry and binding projections;
- add compatibility/version/collision graph validator.

Gate:

- C/Simple/Rust/C++ bindings round-trip fixed test vectors;
- descriptor truncation/extension compatibility matrix passes;
- duplicate/missing/cycle/capability/placement negative cases fail at compile/seal time;
- no private language type appears in public wire records.

Rollback:

- no production path changes; generated data remains shadow-only.

### Phase 2 — Bounded no-GC async kernel

**Purpose:** provide reusable lifecycle and dispatch without unbounded run-phase structures.

Changes:

- generational slot map;
- bounded request/completion/event rings;
- cancellation/deadline tables;
- fixed/chunk arenas;
- lifecycle state machine and generation publication;
- direct/table transport;
- deterministic test scheduler and fault provider.

Gate:

- `NogcBounded` performs zero heap allocations after seal in the instrumented test harness;
- stale handles cannot access reused slots;
- backpressure, cancellation, timeout, drain, and rollback work under concurrency;
- static-direct output equals static-table output;
- disabled/erased plugin leaves no dispatch branch in the tested hot path.

### Phase 3 — Native/SMF adapter and loader convergence

**Purpose:** reuse current provider admission while moving lifecycle authority into the common kernel.

Changes:

- wrap `SimpleProviderQueryV1` and current dynamic loader;
- replace linear live-pin arrays with a bounded generational pin table;
- add multi-provider prepare/shadow/publish generation transaction;
- move runtime build-command synthesis out of `DynSmfSession`;
- emit loader/admission receipts.

Gate:

- digest/signature/capability/ABI/target/symbol failures are typed and fail closed;
- close/unload is impossible with pins or callbacks;
- an incompatible candidate leaves the previous generation active;
- runtime never invokes a compiler for a missing plugin.

### Phase 4 — Unified diagnostic/fix/receipt service

**Purpose:** establish one user-visible truth before migrating rule engines.

Changes:

- normalized diagnostics and related locations;
- transactional text edits/fix groups;
- complete verdict state machine;
- human/JSON/LSP/SARIF adapters;
- coverage and planned/actual receipts;
- deterministic sort/group rules.

Gate:

- one test vector renders equivalent semantic data across all formats;
- warning-only, incomplete, no-input, timeout, crash, and stale-snapshot cases have distinct verdicts;
- malformed offsets and oversized output are rejected.

### Phase 5 — Simple lint shadow adapter

**Purpose:** preserve existing rules while changing infrastructure first.

Changes:

- generate rule descriptors/defaults from declarations;
- wrap existing Simple rule logic behind `LintProviderV1`;
- introduce fact requirements and minimal planner;
- run old and new paths side by side;
- fix summary/verdict correctness immediately.

Gate:

- current clean/error/warning fixture corpus is semantically equivalent except for documented bug fixes;
- every old rule is either mapped or explicitly unsupported;
- every declared rule executes at least one mutation-sensitive fixture;
- no hand-maintained independent known-rule/default table remains authoritative.

### Phase 6 — Simple semantic check convergence

**Purpose:** close the parse-only silent-green class.

Changes:

- fix semantic enforcement/interpreter blockers;
- expose a bounded semantic query/diagnostic provider;
- census current source violations;
- wire `simple check` to required semantic facts;
- retain explicit `--syntax-only` tier;
- converge compile/check/lint diagnostics.

Gate:

- type mismatch, undefined identifier/function, parse error, and clean fixtures have correct verdicts;
- self-hosted and Rust-seed paths agree on the agreed contract corpus;
- semantic tier cost is measured and cached;
- syntax-only output says reduced coverage and never implies semantic cleanliness.

### Phase 7 — Rust worker adapter

Changes:

- worker supervisor and framed/ring protocol;
- Cargo/rustc/Clippy JSON ingestion;
- Cargo metadata/build identity;
- fix/applicability mapping;
- cancellation, timeout, crash containment, and output limits;
- rust-analyzer broker for IDE.

Gate:

- multi-crate workspace, features, target, build-script, warning, error, suggestion, malformed output, cancellation, and crash tests;
- exact toolchain/config identity in receipts;
- no Rust compiler object crosses the ABI.

### Phase 8 — C++ worker adapter

Changes:

- compile database discovery/selection;
- clang-tidy batch worker;
- clangd IDE broker;
- optional libclang narrow adapter;
- fix and related-note mapping;
- header/translation-unit configuration evidence.

Gate:

- missing compile database returns `Incomplete`;
- multiple configurations are represented or explicitly selected;
- diagnostics/fixes map to exact snapshots;
- worker survives malformed/crashing check plugin;
- version-pinned LibTooling checks cannot be loaded under a mismatched toolchain.

### Phase 9 — Editor ExtensionHost adapter

Changes:

- map editor manifests, activation events, command/event registries, lifetimes, permissions, and crash state to kernel contracts;
- generated contribution tables;
- actual worker entrypoint execution through the common supervisor;
- retire duplicate lifecycle authority gradually.

Gate:

- current editor extension tests pass through adapter;
- activate/deactivate disposes every owned registration;
- command/language activation is lazy;
- worker crash disables only its provider;
- generated VS Code projection matches checked-in package data.

### Phase 10 — Common tooling daemon/session

Changes:

- versioned document snapshots/deltas;
- workspace/project/build models;
- language session registry;
- LSP/DAP/test/custom protocol adapters;
- diagnostic/fix cache and cancellation by document version;
- CLI embed/connect mode.

Gate:

- VS Code and SVIM consume the same Simple diagnostic result for one snapshot;
- stale result cannot overwrite a newer document version;
- mixed Simple/Rust/C++ workspace remains bounded and cancellable;
- client disconnect releases leases/tasks.

### Phase 11 — VS Code and native IDE cutover

Changes:

- thin `extension.ts` bootstrap;
- generated contributions and generic providers;
- retain UI-specific custom editor/math/AI/views;
- native tooling client for SVIM/Simple IDE;
- explicit degraded fallback.

Gate:

- capability matrix covers diagnostics, symbols, definitions, references, hover, tokens, folding, fixes, tests, debug, and rich features;
- fallback state is visible and never reports semantic clean;
- extension startup does not start unrelated language workers;
- native and VS Code command/test semantics match.

### Phase 12 — Compiler provider adapter

Changes:

- adapt the coarse `CompilerDriverV1` first;
- use common lifecycle/placement/receipt contracts;
- connect stable query/capsule architecture from the prior plan;
- migrate one low-risk backend provider static, then dynamic;
- preserve existing SCI/provider-query authority.

Gate:

- no central backend factory imports unrelated implementations for the migrated slice;
- static/dynamic provider parity;
- normal incremental flow rebuilds only affected provider/capsule closure;
- compiler help/version loads zero ordinary compiler providers.

### Phase 13 — MDSOC++ framework and pilots

Changes:

- `std.mdsocpp` facade and rules;
- typed command/query/event interfaces;
- product seal and capsule graph validation;
- state migration interface;
- IDE as first large-program pilot;
- second pilot from compiler, web/server, or enterprise app.

Gate:

- no sibling-private dependency violations;
- static product specializes to direct/table dispatch;
- optional plugin removal produces a compile/seal error only for declared required consumers;
- generation rollback preserves state/schema policy;
- ECS remains optional and private to capsules.

### Phase 14 — Wasm component placement

Changes:

- generate WIT from canonical schemas;
- component host adapter and capability mapping;
- async operation mapping to component-model async where supported;
- portable third-party lint/provider SDK.

Gate:

- WIT and native schemas derive from one source and round-trip shared fixtures;
- no ambient filesystem/network/process access;
- resource handles are released;
- Wasm and native implementations pass semantic parity for selected interfaces.

### Phase 15 — Default cutover, cleanup, and release hardening

Changes:

- make new lint kernel authoritative;
- make common tooling session authoritative;
- make editor host adapter the only lifecycle owner;
- delete hard-coded/duplicate registries and runtime build synthesis;
- complete compiler provider migrations by family;
- publish compatibility policy and SDKs;
- full bootstrap/convergence/security/performance release matrix.

Gate:

- one owner each for composition, admission, lifecycle, diagnostics, lint catalog, and IDE language truth;
- no production path depends on shadow/legacy fallback unintentionally;
- rollback to prior signed bundle demonstrated;
- architecture checks prevent reintroduction of duplicate loaders/registries.

---

## 14. Parallel-agent implementation program

### 14.1 Coordination rules

Every agent works in an isolated branch/worktree and records:

```text
starting SHA
integration-base SHA
owned paths
contracts consumed/produced
generated files
production caller proving reachability
planned tests
actual tests and complete failure list
performance/allocation counters expected to change
rollback/deletion gate
unsupported cases
```

Shared files have one owner per wave. Other agents submit contract-change requests plus failing fixtures rather than editing the shared file.

### 14.2 Agent ownership map

| Agent | Ownership | Deliverables | Forbidden ownership |
|---|---|---|---|
| A0 Architecture/integration | decisions, merge order, invariants | frozen contracts, integration receipts | provider business logic |
| A1 Repository evidence/non-vacuity | baseline probes, conflict-marker/reachability gates | Phase 0 evidence | production feature implementation |
| A2 Contract/schema | IDs, versions, wire records, compatibility | V1 contract and bindings | loader/lint semantics |
| A3 Declaration generator | typed declarations, SCI/static registry/bindings/docs generation | deterministic generator | manual provider registry edits |
| A4 Graph/seal validator | dependency/capability/closure/placement/capacity checks | compile/seal diagnostics | runtime scheduler |
| A5 Bounded containers | slot map, rings, arenas, timer structure | no-GC primitives | plugin lifecycle policy |
| A6 Async scheduler | request/completion/event scheduling, cancellation/deadline | deterministic bounded runtime | loader implementation |
| A7 Lifecycle/generation | state machine, pins, publish/drain/rollback | generation manager | dynamic format parser |
| A8 Native/SMF transport | current provider-loader adapters | process-callable path | compiler provider logic |
| A9 Worker supervisor | process lifecycle, protocol, limits, restart/crash policy | reusable worker transport | Rust/C++ semantics |
| A10 Diagnostics/fixes | normalized records, transactional edits | common tooling output model | language-specific analysis |
| A11 Receipts/output | verdict, coverage, human/JSON/LSP/SARIF | output adapters | rule implementations |
| A12 Extended enum compiler | seal tables, identities, exhaustiveness | enum extension integration | lint catalog |
| A13 Lint catalog/planner | declarations, profiles, fact closure, deterministic scheduling | common lint kernel | Simple semantic fixes |
| A14 Simple legacy lint adapter | map current rules and fixes | shadow parity | common contract edits |
| A15 Simple semantic provider | name/type/compiler diagnostics | check convergence | Rust/C++ adapters |
| A16 Rust adapter | Cargo/Clippy/rustc JSON worker | Rust lint provider | worker core |
| A17 Rust IDE broker | rust-analyzer integration | Rust tooling provider | VS Code UI |
| A18 C++ adapter | compile DB, clang-tidy worker | C++ lint provider | worker core |
| A19 C++ IDE broker | clangd integration | C++ tooling provider | native editor core |
| A20 Editor host adapter | manifests/activation/registries/lifetimes | common-kernel mapping | VS Code UI implementation |
| A21 Tooling session/protocol | workspaces/documents/LSP/custom protocol | tooling daemon | language semantics |
| A22 VS Code shell | thin client/generated contribution/UI preservation | VS Code cutover | server analysis |
| A23 SVIM/Simple IDE shell | native client and capability parity | native cutover | buffer authority changes outside agreed API |
| A24 Compiler adapter | coarse driver then provider bridge | compiler pilot | core contract changes |
| A25 MDSOC++ framework | capsule rules/facade/pilot | product framework | duplicate runtime |
| A26 Security/fuzz | malformed wire/artifact/capability/worker/Wasm tests | adversarial gates | feature shortcuts |
| A27 Performance/memory | baselines, allocation and hot-path proof | admission budgets | semantic behavior |
| A28 Test/release | cross-platform/full matrix, rollback/release bundle | release evidence | weakening failed tests |
| A29 Docs/SPipe skills | architecture mirrors, agent/operator guides | durable documentation | claiming unimplemented status |

### 14.3 Parallel waves and merge order

#### Wave 0 — Evidence

Parallel:

```text
A1 current behavior/non-vacuity
A27 startup/dispatch/allocation baseline
A29 architecture/source inventory
A26 malformed/conflict-marker scan
```

A0 freezes the evidence revision.

#### Wave 1 — Contract and generation toolchain

Parallel after a short A2 draft:

```text
A2 stable V1 schemas
A3 declaration/generation prototype
A4 graph/seal validator
A10 diagnostic/edit schema
A11 receipt/verdict schema
A12 extended-enum requirements/probes
```

Merge order:

```text
A2 -> A10/A11 -> A3 -> A4 -> A12
```

Only A2 edits shared wire layouts during this wave.

#### Wave 2 — Runtime substrate

Parallel:

```text
A5 bounded containers
A6 scheduler/cancellation/deadline
A7 lifecycle/generation
A8 native/SMF adapter
A9 worker supervisor
A26 runtime fault tests
A27 allocation/dispatch harness
```

Merge order:

```text
A5 -> A6 -> A7 -> A8/A9 -> A26/A27 gates
```

#### Wave 3 — Lint core and language adapters

Parallel:

```text
A13 catalog/planner
A14 legacy Simple rules
A15 Simple semantic provider
A16 Rust lint worker
A17 rust-analyzer broker
A18 C++ lint worker
A19 clangd broker
A11 output adapters
```

A13 owns generated rule registry; language agents provide declaration inputs only.

#### Wave 4 — IDE convergence

Parallel:

```text
A20 editor host adapter
A21 tooling workspace/protocol
A22 VS Code thin shell
A23 SVIM/Simple IDE client
A26 protocol/fault tests
A27 IDE latency/memory measurements
```

Ordered edge: A20/A21 contract first, then A22/A23 cutover.

#### Wave 5 — Compiler and MDSOC++

Parallel:

```text
A24 compiler driver/provider adapter
A25 MDSOC++ facade + IDE pilot
A12 complete/dyn compiler integration
A27 static/dynamic provider overhead
A28 cross-product matrix
```

#### Wave 6 — Wasm, cleanup, and release

Parallel:

```text
A9/A26 Wasm host/capability containment
A3 WIT generation
A24 additional compiler provider families
A22/A23 legacy fallback deletion
A28 release/convergence/rollback
A29 final docs/skills/status
```

### 14.4 Shared-file protocol

- A2 owns V1 wire files.
- A3 owns generated files and generator output order.
- A4 owns graph/seal validation logic.
- A5 owns generic bounded containers.
- A7 owns generation/lifecycle state.
- A9 owns worker transport/supervision.
- A10 owns diagnostic/edit canonical schemas.
- A13 owns lint planner/catalog generation.
- A20 owns editor-host compatibility adapter.
- A21 owns tooling protocol schemas.
- A24 owns compiler compatibility adapter.
- A25 owns only MDSOC++ rules/facade, never a second runtime.
- A28 may block integration for incomplete failure collection, vacuous tests, or missing rollback evidence.

### 14.5 Agent task template

```text
Objective
Why this lane is independently mergeable
Authoritative owner and paths
Accepted contract/schema versions
Inputs and outputs
Explicit non-goals
Legacy path and shadow comparator
Production caller/reachability proof
Negative control that must fail
Focused tests
Impacted complete test plan
Performance/allocation counters
Rollback/deletion gate
```

Completion report:

```text
Implementation summary
Files changed
Contract changes: none | approved request ID
Generated files and regeneration command
Tests planned/run; all root failures
Mutation/non-vacuity evidence
Performance/allocation evidence
Cross-platform evidence
Known unsupported cases
Integration SHA
Rollback result
```

### 14.6 Parallel testing policy

- agents run isolated focused tests concurrently;
- integration first computes the full test plan and resource classes;
- independent failures continue to the end;
- GPU/LLVM/Clang/Rust/Wasm/high-memory jobs are capacity scheduled;
- planned and actual test IDs/counts are reconciled;
- no lane claims green from zero discovered cases;
- production-caller, mutation, and negative fixtures are mandatory for new registration/dispatch paths.

---

## 15. Test strategy

### 15.1 Contract tests

- fixed binary golden vectors across Simple/C/Rust/C++;
- truncated descriptor and additive-minor compatibility;
- endian/width/alignment checks;
- invalid offsets/lengths/overflows;
- unknown required field/interface/capability;
- schema hash and payload ABI mismatch;
- fuzz decoding and round-trip properties.

### 15.2 Graph/seal tests

- duplicate IDs and aliases;
- missing/ambiguous providers;
- version range mismatch;
- direct and transitive cycles;
- `Critical + Dyn` rejection;
- complete-enum identity collision;
- capability escalation;
- insufficient capacities;
- nondeterministic declaration order producing identical output;
- one-provider specialization.

### 15.3 Runtime tests

- ring full/backpressure/coalescing;
- stale slot/token/pin handles;
- cancel before start/during pending/after completion;
- deadline expiry;
- provider start failure;
- crash/invalid response;
- drain with live requests/listeners/buffers;
- unload refusal while pinned;
- atomic generation swap and rollback;
- repeated load/retire cycles without unbounded growth;
- deterministic scheduler replay.

### 15.4 Lint tests

For every language:

- clean file/project;
- syntax error;
- semantic/type/name error;
- warning-only;
- multiple diagnostics/related locations;
- safe/maybe/conflicting/stale fix;
- suppressed and unknown rule;
- no input;
- skipped file/target;
- missing required build configuration;
- cancellation and timeout;
- provider crash/malformed output;
- cache hit/miss/invalidation;
- output parity across human/JSON/LSP/SARIF.

Specific regressions:

- Simple type mismatch and undefined name cannot pass `check`;
- warning-only run cannot print “all files clean”;
- `--syntax-only` cannot imply semantic coverage;
- missing C++ compile command cannot yield `Clean`;
- Rust build-script/toolchain failure cannot be swallowed as zero diagnostics.

### 15.5 IDE tests

- document open/change/close versioning;
- stale result rejection;
- multi-root and mixed-language workspace;
- provider lazy activation;
- no unrelated worker startup;
- LSP reconnect/restart;
- degraded fallback labeling;
- command/code action/fix parity between VS Code and native IDE;
- test discovery and exact-node execution capability reporting;
- worker crash containment;
- extension deactivate disposal;
- generated contribution mismatch gate.

### 15.6 Extended enum tests

- ordinary/complete/dyn constructors;
- provider qualification mandatory;
- order-independent persistent identity;
- dense-tag generation after seal;
- exhaustive matching over selected complete set;
- critical wildcard/dyn rejection;
- payload schema change invalidation;
- serialization uses persistent ID, never dense tag;
- static and dynamic dispatch parity where both are allowed.

### 15.7 MDSOC++ tests

- sibling-private import prohibition;
- one authoritative command mutation owner;
- query purity/effect declaration;
- event feedback/cycle policy;
- optional dependency absence;
- state migration and rollback;
- direct-call specialization;
- bounded queues and overload policy;
- capsule fault isolation;
- ECS world remains capsule-local.

### 15.8 Cross-platform matrix

At minimum:

```text
Linux x86_64
Windows x86_64
macOS arm64
SimpleOS/QEMU representative static profile
```

Rust/C++ tool adapters record exact installed toolchains. Missing optional toolchains are an explicit unsupported/incomplete lane, not silently skipped green.

---

## 16. Performance and memory plan

### 16.1 Measure before setting numeric thresholds

Phase 0 establishes numeric baselines. Until then, enforce structural budgets:

| Path | Structural budget |
|---|---|
| root help/version | zero ordinary plugins, workers, scans, or runtime compilation |
| erased plugin | zero code/data/dispatch residue in selected binary/path |
| static-direct call | direct/inlined form where optimizer permits; no registry/hash/version work |
| static-table call | dense slot + one indirect call; no string/hash lookup |
| native dynamic call | generational slot validation + one indirect call after admission |
| strict sealed dispatch | zero heap allocations |
| lint no-op edit | recompute only invalidated facts/rules |
| editor keystroke | cancel/coalesce obsolete analysis; never queue unbounded versions |
| worker protocol | bounded frames/batches and output limit |

### 16.2 Required counters

- kernel/provider startup and first-use time;
- query/interface resolution count;
- direct/table/dynamic/worker call counts;
- ring enqueue/dequeue/full/coalesce counts;
- task/request high-water marks;
- arena bytes used/high-water/retained;
- provider-owned and mapped bytes where measurable;
- worker RSS/CPU/I/O;
- files/facts/rules planned/executed/reused/invalidated;
- diagnostic/fix bytes and counts;
- generation pins and drain duration;
- cache key/hash/serialize time;
- UI-to-diagnostic latency by language/provider.

### 16.3 Benchmark scenarios

1. root `--help` and `--version`;
2. lint one clean 20-line Simple file;
3. one Simple type error;
4. warm no-op lint;
5. one-body edit with unchanged public surface;
6. one-rule configuration change;
7. 1k-file mixed-language workspace open;
8. repeated keystrokes with cancellations;
9. Rust workspace Clippy warm/cold;
10. C++ translation unit with/without compilation database;
11. static vs native vs worker implementation of the same synthetic provider;
12. 10k plugin operations under bounded profile;
13. 1k generation reload/drain cycles in stress harness;
14. IDE startup with no source file vs Simple/Rust/C++ file.

### 16.4 Admission policy

A performance claim must name:

```text
repository SHA
binary/provider/composition digests
toolchain versions
host and OS
profile/placement
cache state
corpus
iterations/warmup
observer mode
median and tail results
allocation/RSS evidence source
```

Do not infer per-plugin RSS from process RSS. Use provider-owned arenas/tags and worker isolation for attribution.

---

## 17. Robustness and operational behavior

### 17.1 Failure taxonomy

```text
ConfigurationError
CompositionError
CompatibilityError
AdmissionError
CapabilityDenied
ResourceBudgetExceeded
Backpressure
Cancelled
TimedOut
ProviderFault
ProtocolViolation
ToolchainFailure
IncompleteAnalysis
StaleSnapshot
StateMigrationFailure
RollbackFailure
```

Every error identifies owner, phase, plugin/provider/generation, operation, and whether retry/fallback is allowed.

### 17.2 Retry policy

- deterministic configuration/schema errors: never retry automatically;
- backpressure: caller may retry/coalesce by operation policy;
- cancellation/stale snapshot: normal, no crash count;
- worker transient exit: bounded restart only when policy allows;
- native provider crash: process containment is impossible; prefer worker for untrusted/unstable code;
- protocol violation: disable generation and rollback;
- timeout: cancel, drain, and count toward health policy;
- critical provider failure: fail product operation rather than silently substitute a weaker provider.

### 17.3 Observability

`simple plugin inspect`, `simple lint receipt`, and IDE status surfaces should expose:

- selected product composition;
- active/shadow/retired generations;
- interface bindings and placement;
- capability grants;
- queue/arena budgets and high-water marks;
- health/crash/restart state;
- lint fact/rule coverage;
- stale/degraded language-provider state;
- exact reasons for load, skip, fallback, cache reuse, or invalidation.

---

## 18. Migration and rollback discipline

### 18.1 Four-step cutover for every subsystem

```text
1. Adapt: old implementation emits/consumes new contract.
2. Shadow: old and new execute on a bounded corpus; compare receipts/results.
3. Select: new path optional by composition/profile/flag, with prior generation retained.
4. Default/delete: only after production reachability, mutation, parity, and rollback evidence.
```

### 18.2 No broad rewrite commits

Separate commits for:

- contract/schema;
- generator output;
- adapter;
- production call-site wiring;
- tests;
- default switch;
- deletion.

This makes bisect and rollback possible and reduces parallel-agent conflicts.

### 18.3 State compatibility

A plugin generation that owns persistent state declares:

- state schema ID/version;
- forward migration function/provider;
- rollback compatibility window;
- transactional migration/checkpoint behavior;
- whether old generation may continue reading new state.

Do not publish a generation whose state migration cannot be rolled back under the product policy.

---

## 19. Acceptance criteria

### 19.1 Kernel Plugin Library

- one canonical SCI/provider-query/composition authority;
- one lifecycle/generation authority;
- fixed-width stable boundary with no private language layouts;
- generated static registries and bindings;
- compile/seal-time graph, version, capability, closure, placement, and capacity errors;
- strict bounded profile with zero post-seal heap allocation in the instrumented harness;
- static direct/table/native/worker semantic parity for representative interfaces;
- atomic generation publication and proven rollback;
- no unload with live pins/requests/callbacks/buffers;
- no runtime compilation of missing providers.

### 19.2 Lint

- one rule catalog/config/verdict/diagnostic/fix/receipt model;
- Simple, Rust, and C++ adapters available;
- `simple check` reports name/type errors in its default semantic contract;
- warning-only is never called clean;
- no-input/incomplete/tool failure cannot silently pass CI/critical mode;
- language adapters expose exact toolchain/build/snapshot coverage;
- CLI/LSP/JSON/SARIF outputs derive from identical records;
- fixes are hash-checked, transactional, and conflict aware;
- incremental scheduling is fact based and observable.

### 19.3 IDE

- VS Code and native IDE consume the same authoritative tooling sessions;
- heavy analysis is not duplicated in the VS Code activation root;
- standard features use LSP/DAP/test protocols where possible;
- generated UI contributions match plugin declarations;
- worker and external entrypoint execution is real and contained;
- degraded fallback is explicit;
- Simple/Rust/C++ mixed workspaces work without one universal AST;
- stale document results cannot overwrite current state.

### 19.4 MDSOC++

- product graph is typed and sealed;
- static/complete/dyn semantics are explicit;
- cross-capsule interaction uses typed commands/queries/events/streams;
- no direct sibling-private dependencies;
- hot internal capsule calls remain ordinary direct calls;
- ECS is optional and capsule local;
- lifecycle/capability/receipt/runtime are reused from the common library, not duplicated;
- at least two large-program pilots pass rollback and performance gates.

### 19.5 Parallel implementation

- shared V1 schemas and generated registries each have one owner per wave;
- every lane supplies a negative control and production reachability proof;
- full selected test failures are collected, not stopped at the first independent failure;
- no green result with zero planned/executed cases;
- every merge identifies the exact integration SHA and rollback selector.

---

## 20. Decision log

| Decision | Rationale |
|---|---|
| Reuse `nogc_sync_mut.composition` | it already contains the accepted SCI/provider-query wire foundation |
| Add async layer in `nogc_async_mut.kernel_plugin` | lifecycle/scheduling/cancellation are reusable and should not contaminate the stable sync codec core |
| Keep `SimpleProviderQueryV1` | avoids a competing loader/discovery protocol |
| Separate closure from placement | permits sealed products with separately packaged providers and prevents in-process `dyn` from masquerading as complete |
| Static-first generated dispatch | minimizes overhead and maximizes compile-time checking |
| Worker-first Rust/C++ deep integration | compiler internals are version coupled; process isolation and structured output are safer |
| LSP for editor features | reusable across VS Code/native editors; avoids UI-specific analysis implementations |
| SARIF output | standard CI/static-analysis interchange |
| Extended enums for semantic extension points | current grammar already models complete and runtime-open extension |
| Generated rule/contribution registries | removes hand-maintained duplicated truth |
| Explicit incomplete/no-input verdicts | prevents silent green |
| MDSOC++ is a facade/rule set over kernel plugin | avoids a second runtime and keeps architecture composable |
| No new grammar in Phase 1 | reduces compiler-core risk; existing declarations/SDN/extended enums suffice |
| Wasm optional after worker path | valuable for untrusted portability, but not required for first low-overhead trusted path |

---

## 21. Immediate first implementation slice

The smallest end-to-end slice that proves the architecture is:

1. Define common plugin IDs, closure/placement, diagnostic, text edit, receipt, and lint provider V1 records.
2. Generate a static registry for two providers:
   - `lint.common.text` with one source-text rule;
   - `lint.simple.legacy` wrapping a small existing Simple rule set.
3. Implement bounded direct/table dispatch and a fixed diagnostic arena.
4. Add verdicts `Clean`, `Warnings`, `Errors`, `Incomplete`, and `NoInput`.
5. Run old/new lint paths in shadow mode on clean, warning-only, error, parse-error, and zero-input fixtures.
6. Fix the CLI renderer so warning-only cannot say clean.
7. Emit human, JSON, and one minimal LSP diagnostic projection from the same records.
8. Add a generated VS Code command/contribution entry consuming the same declaration.
9. Add one SVIM/native client probe consuming the same diagnostic record.
10. Measure allocations and direct/table overhead.

This slice intentionally avoids dynamic loading, Rust, C++, and full semantic check. It proves contract generation, static dispatch, lint convergence, and two editor shells before the larger parallel waves proceed.

The next slice adds the semantic Simple provider; then Rust and C++ workers can proceed in parallel.

---

## 22. Research sources

### Repository and prior design

- Simple repository baseline: <https://github.com/ormastes/simple/tree/43a4a491c3b5ab8bd350a09a2541a726213053a2>
- Current accepted composition architecture: `doc/04_architecture/minimal_bootstrap_configuration_composed_dynamic_architecture.md`
- Provider wire contract: `src/lib/nogc_sync_mut/composition/provider_contract.spl`
- Provider loader/admission: `src/os/smf/provider_loader.spl`
- Provider activation: `src/os/smf/provider_activation.spl`
- Current dynSMF session: `src/os/smf/dynsmf_session.spl`
- Editor ExtensionHost: `src/lib/editor/extensions/host.spl`
- IDE extension campaign state: `.spipe/ide_extension_kernel/state.md`
- VS Code extension: `src/app/vscode_extension/`
- SVIM architecture: `doc/04_architecture/app/tools/svim.md`
- Unified editor backend campaign: `.spipe/unified-editor-backend/state.md`
- Current Simple lint: `src/compiler/90.tools/lint/`
- Parse-only check defect: `doc/08_tracking/bug/check_silently_passes_type_errors_parse_only_2026-09-01.md`
- Enum extension grammar tests: `test/01_unit/compiler/frontend/enum_extension/enum_extension_grammar_spec.spl`
- Completeness design: `doc/05_design/compiler/hardening/critical_completeness_design_2026-08-21.md`
- MDSOC/MDSOC+ reference: `.claude/memory/ref_architecture.md`
- Prior recovered plan: `simple_compiler_kernel_plugin_bootstrap_refactor_plan_2026-08-30.md`

### VS Code and language protocols

- VS Code Extension Anatomy: <https://code.visualstudio.com/api/get-started/extension-anatomy>
- VS Code Extension Host: <https://code.visualstudio.com/api/advanced-topics/extension-host>
- VS Code Language Server Extension Guide: <https://code.visualstudio.com/api/language-extensions/language-server-extension-guide>
- Language Server Protocol 3.17: <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/>

### Rust

- Clippy adding lints: <https://doc.rust-lang.org/clippy/development/adding_lints.html>
- Clippy lint passes: <https://doc.rust-lang.org/clippy/development/lint_passes.html>
- Cargo external tools/JSON messages: <https://doc.rust-lang.org/cargo/reference/external-tools.html>
- rustc JSON output: <https://doc.rust-lang.org/rustc/json.html>
- rust-analyzer manual: <https://rust-analyzer.github.io/manual.html>
- `rustc_public` current documentation: <https://doc.rust-lang.org/nightly/nightly-rustc/rustc_public/index.html>

### C++ and LLVM

- Clang tooling interface selection: <https://clang.llvm.org/docs/Tooling.html>
- clang-tidy: <https://clang.llvm.org/extra/clang-tidy/>
- LibTooling: <https://clang.llvm.org/docs/LibTooling.html>
- libclang: <https://clang.llvm.org/docs/LibClang.html>
- JSON compilation database: <https://clang.llvm.org/docs/JSONCompilationDatabase.html>
- clangd compile commands: <https://clangd.llvm.org/design/compile-commands>
- clangd diagnostic code walkthrough: <https://clangd.llvm.org/design/code>
- LLVM New Pass Manager: <https://llvm.org/docs/NewPassManager.html>

### Portable/sandboxed plugin ABI

- WebAssembly Component Model WIT: <https://component-model.bytecodealliance.org/design/wit.html>
- Canonical ABI: <https://component-model.bytecodealliance.org/advanced/canonical-abi.html>
- WIT worlds: <https://component-model.bytecodealliance.org/design/worlds.html>
- Component-model concurrency/async ABI: <https://github.com/WebAssembly/component-model/blob/main/design/mvp/Concurrency.md>
- WASI 0.3 announcement: <https://bytecodealliance.org/articles/WASI-0.3>

### Static-analysis interchange

- SARIF 2.1.0 OASIS standard: <https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html>

---

## Final recommendation

Proceed with the Kernel Plugin Library as a convergence layer, not a replacement project. Preserve the existing SCI/provider query, editor contribution host, lint rules, VS Code UI, SVIM editor core, and compiler provider plan. Move their duplicated lifecycle, registration, scheduling, diagnostic, and placement concerns into one reusable no-GC async kernel through compatibility adapters and shadow cutovers.

The highest-priority correctness work is the common verdict/coverage model and Simple semantic check provider. The highest-priority architecture work is the generated contract graph plus bounded async runtime. Rust and C++ support should use workers and existing language tooling first. MDSOC++ should be introduced only after the common kernel has proven itself in lint and IDE pilots.
