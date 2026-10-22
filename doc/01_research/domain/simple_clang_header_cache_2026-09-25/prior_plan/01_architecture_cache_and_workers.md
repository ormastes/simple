# Report 1 — Unified build, cache, resource-sharing, and worker architecture

**Decision date:** 2026-09-25  
**Project:** Simple language and platform  
**Status:** Proposed implementation plan; no compiler, workflow, hook, or repository setting was changed by this report.  
**Evidence baseline:** Simple commit `ed75897fe050d874ce7c7bcd90c2b30953ad65ce`. Current-state findings are in Report 3.  
**Notation:** New command names, interfaces, configuration fields, and resource formats below are proposals unless explicitly identified as existing.

## 1. Final decisions from the complete session

| Concern | Final decision |
|---|---|
| Repository | Monorepo for tightly coupled first-party code; optional, commit-pinned external examples and dependencies. |
| Incrementality | One compiler-authoritative, typed dependency graph, with build and test views. |
| Fast feedback | Warm ordinary-change preflight P95 below 60 seconds, without claiming unfinished work passed. |
| Scheduler topology | Main scheduler → node agent → persistent grouped mid-scheduler processes → compilation threads. On one machine the main scheduler and node-agent roles may share a process. |
| Mutable startup state | Keep group-local, concurrency-safe file/resource indexes and allocator pools warm. Mutable sharing is supported, not prohibited. |
| Cross-process sharing | Share immutable payload mappings by default; permit explicitly designed process-shared mutable coordination and exclusive-owned regions. |
| Fault containment | A group is a failure domain, not each thread. Separate executor processes remain the fallback for unsafe providers, tests, untrusted work, hard isolation, and retries. |
| Protocol | SDN for native control, metadata, manifests, and receipts. Binary for bulk payloads and an optional versioned local shared-memory transport. |
| Compiler integration | Common ResourceShare interface; Simple-native summaries and Clang-native serialized resources, not a shared live AST ABI. |
| Distribution | Same action model locally and remotely; native execution and cross-compilation requirements are distinct. |
| Release | Build immutable candidates, validate exact artifacts, then promote; full clean bootstrap remains a distinct qualification job. |

This settles the earlier alternatives: do not default to one fresh process per file, and do not execute arbitrary tests or unaudited compilers inside the trusted scheduler. Grouped compilation is the intended fast path **after provider qualification**, not an assumption that every existing compiler entry point is reentrant.

## 2. Architecture and ownership

```text
CLI / IDE / local hooks / GitHub adapter
                  |
       Snapshot + dependency planner
                  |
         Typed action/test DAG
                  |
     Main scheduler + durable attempt ledger
                  |
          SDN authenticated control
          /                       \
   Local node agent          Remote node agents
          |
          +-- group process: Simple toolchain digest A
          |      +-- mid-scheduler/control loop
          |      +-- group-local mutable ResourceState
          |      +-- shared resource mappings
          |      +-- compile threads, private contexts
          |
          +-- group process: qualified Clang digest B
          |      +-- scanner/resource service
          |      +-- compile threads, private AST/LLVM contexts
          |
          +-- isolated executors: tests, linkers, plugins, retry
                  |
       Verified publication broker / existing CAS
```

The main scheduler owns jobs, dependencies, priorities, attempt leases, and accepted outcomes. It does not load compiler providers. A node agent owns machine capacity and process trees. A group owns one compatible toolchain/runtime/provider environment and a bounded thread pool. A publication broker validates result manifests and fences before updating shared action mappings. The broker may be a small service in the node agent; it must not accept arbitrary worker writes as authoritative.

Use Simple's existing kernel/plugin approach to separate providers from scheduling policy. The core interfaces cover immutable identities, DAG state, cancellation, resources, result validation, and telemetry. Host execution, shared mappings, toolchain loading, compiler providers, and remote transports are adapters. Extend existing cache and target modules rather than introducing a second CAS or competing action-key encoder. Existing canonical identities already have a defined encoding and field ordering. [R05]

### Group identity

A proposed `GroupKey` includes provider binary digest, provider ABI/schema, host execution environment, runtime/allocator family, security tenant/trust class, and any options that change process-global state. A target family can split groups where the provider needs it. It is not necessary to create a group for every source revision: action/resource keys distinguish those revisions. Never reuse a loaded library under a changed toolchain digest; drain the old group and start a new one.

A group key is an execution-pool identity, **not** an action cache key. A raw-source payload may be shared across compatible tools even when their group keys differ. A parsed or semantic resource normally requires the exact provider/schema/options key.

### Group size and scheduling

Start qualification with small configurable groups, for example 2–4 active compilations, and benchmark 1, 2, 4, and 8. These are experiments, not measured optimal values. Reserve control/I/O capacity outside the compilation pool. Account for each compile's inner backend parallelism; eight outer threads each starting eight backend workers is not an eight-core workload.

Admission must satisfy CPU tokens, memory estimates, current pressure, file-descriptor limits, and exclusive resources. A useful starting memory constraint is:

`group_limit >= base_resident + shared_cache_budget + sum(active_private_estimates) + reserve`.

Measure PSS/unique memory or equivalent accounting; summing RSS across mmap-sharing processes double-counts pages. Avoid using a single high-contention global cache lock. Shard group-local maps and keep per-action scratch allocators private. NUMA grouping and node-local caches are later measured optimizations, not mandatory affinity everywhere.

## 3. Action identity: complete inputs before fast reuse

### Three separate identities

**ActionSpec** identifies the requested computation: compiler/tool closure, explicit and discovered input roots, ordered arguments, meaningful environment, target, outputs, and relevant configuration.

**AttemptSpec** identifies one execution: job/attempt IDs, lease/fence, selected node/group, resource allocation, queue priority, transport, and deadlines.

**ValidationSpec** identifies evidence requirements: tests and cases, runner, fixture/runtime closure, execution class, seeds, timeout policy, isolation requirements, and qualification level.

Do not put branch names, worker IDs, retry counters, or cache locations in the computation key. Conversely, an execution setting that can affect outputs cannot be omitted merely because it looks operational. Initially key compiler thread-count/algorithm options conservatively; remove a field only after its irrelevance is established. For time-sensitive tests, a changed timeout or environment produces different validation evidence. An optional external-protocol adapter must preserve the external protocol's own key semantics rather than pretending its keys equal Simple's.

### Canonical SDN and existing encoders

Author metadata and wire messages in SDN. Parse them into a versioned typed schema. Derive digests through the existing canonical-identity machinery, or a deliberately versioned successor with migration tests. Do not hash whitespace-sensitive SDN rendering as the semantic identity and do not introduce ad hoc string concatenation. Preserve ordering for argument lists, include search paths, resolver probes, link order, and other semantically ordered fields. Sort only sets.

Reject duplicate fields, invalid lengths, unknown mandatory fields, unsafe paths, integer overflow, unsupported schema versions, and inconsistent binary descriptors. A manifest's self-digest/signature fields are outside its hashed payload. Define byte-length, UTF-8, optional-field, and default-value handling once, including cross-language golden vectors. Report 4 gives proposed SDN envelopes and binary contracts. [R05]

### Authoritative InputManifest

Every action requires a snapshot-bound manifest containing input contents, stable paths, executable bits, symlinks where meaningful, tool/SDK/library roots, generated inputs, and resolver witnesses. File timestamps can accelerate change detection but are not the authority for remote reuse. The scanner must record relevant negative dependencies: a previously absent higher-priority header/module candidate appearing can change name resolution.

For dynamic discovery, run an explicit scan/planning action first, or execute against a hermetic snapshot that captures and validates the read set before publication. Generated inputs are producer actions, not accidental files found in the developer checkout. Reconcile declared and actual input consumption before admitting a result. Hermetic build designs isolate tools and inputs to avoid machine-specific behavior. [W10]

**Current P0:** the inspected target executor deliberately has no authoritative action digest, disables target-level reuse, and rejects dependency-bearing targets because `native-build` cannot consume an input manifest. Complete that connection before enabling the new reuse path. Do not replace its fail-closed result with a guessed hash. [R02]

## 4. Dependency tracking: compilation and testing are different

Use one graph with typed edges and several query policies. Preserve old and new graph snapshots so deleting a symbol, moving a file, changing an import, or removing an aspect cannot erase the dependency that must be invalidated.

| Edge/facet | Trigger | Required response |
|---|---|---|
| Implementation | Provider body changes | Rebuild provider; relink/reload where applicable; select behavior-dependent tests. |
| Compile interface | Consumer requirement is no longer satisfied | Re-resolve/type-check/recompile affected consumers. |
| ABI/layout | Calling convention, layout, discriminant, vtable changes | Rebuild or reject incompatible object/runtime consumers. |
| Compile semantics | Macro, CTFE, template, inline, optimization, or aspect semantics change | Regenerate semantic consumers. |
| Resolution | Candidate set/order/absence changes | Re-run affected resolution and consequent actions. |
| Tool | Compiler, linker, generator, provider implementation changes | Invalidate actions produced by that tool unless a qualified finer tool closure exists. |
| Runtime/test behavior | Executed implementation or loaded library changes | Re-run dependent tests even if ordinary source interfaces are identical. |
| Fixture/configuration | Data, schemas, environment contracts, setup code change | Invalidate test/build actions that consume them. |

The existing interface-compatibility plan already separates implementation, compile-interface, ABI, and compile-semantic identities. Preserve that direction. Rust's red/green model is a useful reference for stopping propagation when a recomputed query result has the same fingerprint. [R11] [W11]

**Correction to the earlier discussion:** a body-only change is not a general license to run only the provider's unit tests. Its callers may need no recompilation yet still behave differently. Test selection must follow runtime implementation dependencies, declared feature/layer contracts, and conservative fallback scopes.

### `.tld`, `.rr`, and `.sreq`

Use the established `.tld` interface-summary concept, `.rr` reverse dependencies, and `.sreq` consumer requirements rather than introducing a competing `.tldr` file extension. “TLDR” in the discussion means the interface-summary role. Generated records need schema, source/snapshot, provider, target/configuration, and completeness evidence. They are rebuildable cache/index data, not handwritten authoritative dependency lists.

A `.tld` digest can be exact while the provider's implementation digest changes. A consumer-specific compatibility check can preserve an old compile result only when all recorded requirements remain satisfied. `Unknown` must broaden/rebuild. Never treat a line-based declaration summary, historical test coverage, or Bloom filter as a sound negative proof on its own. The inspected textual extractor explicitly omits struct/class field lines; that is an unsafe basis for layout-sensitive compilation avoidance. [R05]

Keep broad conservative target closures as the production fallback until precise edges are certified against full builds. Include generic instantiation, trait candidate absence, overload selection, AOP selection and non-selection, generated source, effect/capability changes, and compiler live-source dependencies in the mutation tests.

## 5. Cacheability research and final cache matrix

There are two different optimizations: **resource reuse** avoids repeated startup/parse work, while **action reuse** avoids executing the computation at all. ResourceStore holds immutable bytes; ActionCache maps a complete computation identity to a validated result. A mutable directory pointing to immutable objects is not the same as mutable artifact contents. Bazel documents the analogous distinction between content-addressed outputs and action-result lookup. [W09]

| Resource/action | Reuse scope | Key requirements | Policy |
|---|---|---|---|
| Raw source and fixtures | Threads/processes/hosts | Exact bytes, path semantics in consuming action | Cache broadly within authorization scope. |
| File metadata and existence probes | Snapshot/group | Snapshot ID + resolver/search context | Advisory unless immutable-snapshot bound. |
| Token streams/parse trees | Provider-compatible consumers | Source bytes, grammar/parser version, lexical options, encoding | Cache frozen representation; no untracked pointers. |
| Simple `.tld`/`.sreq` | Compatible schema/toolchain | Full type/interface/configuration and semantic dependencies | Enable only after authoritative extraction. |
| `.rr`/target/test graph | Snapshot/configuration | Source/config roots, scanner version, completeness evidence | Derived index; rebuild on uncertain history. |
| Clang PCH/preamble | Compatible prefix context | Compiler/configuration/header closure and validated preprocessor context | Binary reuse; private deserialization state. |
| Clang header module PCM | Declared module context | Module map, headers, macro/options/target/compiler closure | Build once per valid context. |
| Standard C++ module BMI/PCM | Explicit module DAG | Exact compiler/configuration, imports, interface inputs | Separate module action and dependent compile actions. |
| Simple typed HIR/MIR | Same semantic configuration | Tool/schema/input roots and all relevant semantic facets | Frozen snapshots; keep mutation private or exclusively owned. |
| Optimizer analysis | Function/region/pass scope | Stable IR identity, pass version, target/options, dependency assumptions | Later optimization; whole-function fallback first. |
| Object/SMF/library | Full action scope | Authoritative tool and input closure | Cache only validated successful outputs. |
| Link/archive/LTO result | Full ordered link action | Objects, archive order, scripts, linker/plugins, SDK/runtime, flags | Cacheable if deterministic; memory-heavy actions may run isolated. |
| Deterministic generators | Hermetic action | Generator/tool/data/env closure | Cacheable; no implicit network/time. |
| Lint/architecture checks | Exact analyzed snapshot | Rule/policy/baseline/tool and graph roots | Cacheable; policy changes invalidate evidence. |
| Pure hermetic unit/contract tests | Exact validation scope | Test executable, runtime, fixtures, runner, seeds, relevant config | Cache successes; record that evidence was reused. |
| Integration tests with isolated fixtures | Qualified environment | Fixture setup/teardown identity and runtime/execution class | Conditional caching, normally short-lived validation policy. |
| Native OS/driver/hardware tests | Actual execution environment | Host kernel/driver/firmware/device profile and test closure | Reuse build artifact, normally rerun test. |
| Fuzz/stress/race/soak tests | Specific run/campaign | Instrumentation, seeds/corpus, schedule and environment | Preserve results; do not replace required new coverage with an old pass. |
| Performance tests | Measurement environment | Hardware, governor, load, tool/config, inputs | Compile cache allowed; rerun measurements. |
| Bootstrap convergence | Qualification DAG | Seed, source, toolchains, stages, deterministic settings | Stage artifacts reusable; an independent clean qualification must actually rebuild. |
| Signing, release publication, power-cycle/reset | Side-effecting operation | Explicit operation identity and authorization | Not an ordinary cache hit or speculative retry. |

No cache hit is valid simply because a file exists or a previous branch was green. Compiler failures and failed tests are retained as evidence, not placed in the successful action cache. Optional short-lived diagnostic deduplication must be explicitly separate and cannot manufacture green CI.

### Clang-specific limits

PCH/modules serialize parsed and semantically analyzed state, with lazy loading into each compilation. They can avoid repeated header parsing, but their creation can also become a build critical path. [W02]

Header modules and standard C++ modules are different mechanisms. Ordinary textual headers are not universally convertible to independent cached AST fragments: include order, macros, pragmas, lookup context, generated headers, and target options matter. Start with controlled PCH prefixes or declared modules; retain textual preprocessing for unsupported headers. [W03] [W04]

Do not enable ccache “sloppiness” options to satisfy a timing objective. Its current manual explicitly describes limitations around PCH and modules, including settings that relax dependency checking. The new Simple action cache should key the actual module artifacts and complete inputs instead of assuming an external object-cache wrapper solves module correctness. [W12]

## 6. ResourceShare interface for Simple and Clang

Separate four responsibilities:

| Interface | Responsibility |
|---|---|
| `ResourceStore` | Lookup, pin, map, verified publication, eviction of immutable payloads. |
| `ResourceState` | Single-flight construction, readiness/failure state, waiters, owners, leases. |
| `CompilerProvider` | Discover dependencies; produce/consume resources; compile within an explicit per-action context. |
| `ExecutionContext` | Snapshot filesystem, toolchain, outputs, diagnostics, cancellation, resource budgets, action identity. |

A proposed provider contract is:

```text
capabilities() -> supported resources, isolation modes, reentrancy qualification
open_group(group_config, resource_service) -> group_context
begin_action(action_spec, snapshot_fs, output_sink) -> private action_context
scan(action_context) -> input/resolution manifest
prepare_resource(action_context, resource_request) -> candidate resource
compile(action_context, acquired_resources) -> candidate outputs
cancel(action_context) -> acknowledged / unsupported
end_action(action_context) -> reset report
close_group(group_context)
```

`ResourceShare` operations include `lookup`, `acquire_or_build`, `pin`, `map`, `publish_candidate`, `release`, and `explain_miss`. A returned resource carries provider/format version, digest, length, access mode, snapshot constraints, and lifetime token. Across an FFI boundary use a versioned C ABI with explicit sizes and ownership; do not expose C++ STL objects, Clang pointers, or a Simple heap object layout as a cross-process ABI.

The service can return a process-local pointer only for an in-process mapping with a valid lifetime token. Cross-process consumers receive a region/object handle plus offset/length/generation; a numeric OS handle printed in SDN is not a portable capability transfer. Transfer the actual handle through the host-supported channel and bind it to the SDN request.

### Provider rollout

**Simple:** isolate all action-owned compiler state, audit global tables/registries, and provide explicit thread-safe resource access. Qualified immutable parsed/type summaries can later be shared more deeply than a generic serialization layer.

**Clang:** first integrate external compiler processes with the shared snapshot/resource store and explicit PCH/PCM actions. Then add an in-process adapter for a pinned Clang build. Each concurrent invocation has its own `CompilerInstance`, mutable frontend state, diagnostics, and `LLVMContext`. clangd documents that its preamble bytes are thread-safe but its live AST is not, even for read-only access. LLVM explicitly supports parallel independent contexts. [W01] [W05]

The dependency-scanning service is a concrete API integration point, but use the headers and capabilities of the **pinned toolchain**, not a hard-coded namespace from an older LLVM release. [W06]

Do not call a command-line `main()` concurrently and call that a compiler service. Audit command-line globals, working directory changes, environment mutation, plugin registries, signal handlers, process-global diagnostics, temporary names, LLVM shutdown, and linker entry points. Process-wide initialization runs once; shutdown occurs only after the group drains. An unqualified component stays out of process.

## 7. Mutable startup data and cross-process sharing

### Within a group process

Thread-shared mutable caches are ordinary concurrent in-process structures. They can retain file indexes, single-flight records, parsed-resource handles, allocator free lists, and dependency lookup accelerators. Route policy changes through the mid-scheduler, but do not require an SDN RPC or manager lock for every cache hit.

Cache entries should normally publish stable payloads. Per-compilation AST transformations, inference state, diagnostics, and temporary arenas belong to that compilation, even when its input bytes came from a shared cache. Reused thread contexts must clear semantic state, not merely reset a bump pointer while leaving stale references in a map.

### Between group processes

Multiple processes can read and write a shared mapping; `MAP_SHARED` makes writes visible, while `MAP_PRIVATE` creates copy-on-write private modifications. Windows supports shared mappings and interlocked operations on variables in shared memory. These mechanisms do not themselves provide high-level consistency or protect against a bad writer. [W13] [W15] [W16]

Use three access classes:

* **Immutable resource:** readers map verified source/module/object data read-only; publishers create a new object instead of overwriting an existing digest.
* **Controlled shared mutation:** a small ring, ready-state table, counters, or fixed-layout directory uses an explicitly tested interprocess synchronization ABI.
* **Exclusive-owned mutable region:** one action owns a relocatable region; ownership transfer requires synchronization, quiescence of old users, and a new generation/fence.

The latter is an option for custom Simple representations, not permission to move a Clang `ASTContext` to another process without serialization. Pointer-rich process heaps, vtables, mutex implementations, and allocator metadata are not automatically relocatable.

**Correction to the earlier isolation claim:** two processes with write access to the same data are not fully isolated from each other's corruption. Do not give compiler groups writable access to the scheduler's authoritative ledger or unrestricted mutation of other groups' cache indexes. Prefer manager-mediated publication and per-owner staging. Cross-group mutable indexes must be discardable/rebuildable or transactional.

### Platform contract

Expose mapping, handle passing, process lifetime, robust synchronization, and process-tree containment through sosix. Validate atomic width, alignment, memory ordering, and process-shared behavior on each supported host. Do not assume all language `Atomic<T>` implementations or fallback locks work across processes. Use a lock-free interprocess ABI only where explicitly supported; otherwise use the host's process-shared primitive or a broker.

On owner death a robust mutex signals inconsistent protected state; it does **not** repair the data automatically. The recovery code must validate/rebuild or mark it unusable. [W14] Linux cgroups and Windows Job Objects are useful containment adapters for resource budgets and child-process cleanup. They do not make concurrent threads separate security principals. [W17] [W18]

Avoid retaining writable hardlinks into the CAS, mmap of a live mutable checkout as if it were immutable, shared raw addresses, PID-only ownership, unbounded pinned generations, and eviction based on unprotected reference counts. A mapping must remain backed by valid immutable storage for its full lease.

## 8. Single-flight, publication, and eviction

Proposed state machine:

```text
MISSING -> BUILDING(owner_epoch, attempt, lease)
        -> CANDIDATE -> VALIDATING -> READY(digest, generation)
        -> FAILED / ABANDONED
READY -> RETIRING -> RECLAIMABLE
```

One producer builds a resource; other requests attach waiters. A canceled waiter detaches without canceling a still-needed shared build. Waiting for dependencies releases execution tokens so every thread cannot deadlock waiting for work queued behind itself. Detect resource-build dependency cycles.

A producer writes to an attempt-private path/arena, reports exact bytes, and proposes a manifest. The publication broker verifies canonical manifest hashing, all referenced payload digests and lengths, completeness of output/input closure, trust policy, schema compatibility, and the current attempt fence. Only then may it install the action mapping. Publication is atomic with respect to readers; durable publication additionally uses the platform's required persistence steps.

Retirement separates removing an index entry from reclaiming mapped bytes. Leases/epochs protect live readers. Crash cleanup cannot reuse a slot while a paused old process may still access it. A timed-out owner must be fenced from publication and confirmed stopped before unsafe local reuse; network lease expiry alone is not proof that a machine or hardware operation stopped.

Add bounded caches for negative lookups tied to immutable snapshots; otherwise a generated file appearing could invalidate them. Limit startup prefetch by observed use and memory budget, rather than loading all headers or the entire repository on every group launch.

## 9. Distribution and exact tool/library versions

Worker registration advertises execution OS/architecture, available capacity, sandbox classes, target capabilities, device profiles, supported protocol/provider schemas, and trusted toolchain stores. A user can request a version alias; the planner resolves it to a lockfile's exact compiler, libraries, SDK, sysroot, linker, and plugin digests before scheduling.

Separate **where the compiler runs**, **what it generates**, and **where the result is tested**. A Linux executable cross-compiler may produce a Windows artifact; that does not prove Windows-native test coverage. Emulated RV64, physical RV64, and SimpleOS/QEMU runs have different validation labels and evidence. Proprietary SDK/tool licenses may constrain worker selection and redistribution.

Native agents on Windows/macOS/FreeBSD and later SimpleOS use the same protocol. Kubernetes or the proposed Simple orchestrator can provision persistent worker capacity; it should not create a new pod for every tiny compile. Kubernetes affinity/labels are an infrastructure mechanism, not a substitute for toolchain and trust verification. [W26]

Idle-host contribution is opt-in with CPU/RAM/temperature/time-window limits, prompt preemption, scoped credentials, and no access to unrelated files. Do not run arbitrary public PRs on a developer workstation. Keep trusted, fork-PR, and release pools separate.

### Placement policy

Choose eligible nodes first, then prioritize interactive/merge-critical work, critical-path actions, resource/tool locality, predicted completion time, and fair-share aging. Avoid starving nightlies indefinitely. Coalesce tiny actions when setup/transfer dominates, while preserving action identities and per-action results. Module builds that unblock many compilations may deserve earlier scheduling than independent leaf compiles.

A local/remote race is optional for pure hermetic actions with separate output staging and bounded duplicate work. It is forbidden for signing, publishing, device mutation, or tests with external side effects. Only one fenced result is admitted. If equal complete keys yield different output digests, retain both, quarantine the mapping, and investigate rather than silently selecting a winner.

## 10. Performance claims and qualification

The design removes IPC from intra-group cache access: the compilation threads are real threads in one address space. That makes thread-like hot-path costs plausible, not a measured guarantee. Lock contention, allocator behavior, lazy deserialization, memory bandwidth, group restart costs, and cache locality can dominate.

Compare fresh-process-per-action, warm singleplex processes, grouped threads, and grouped threads with shared resources on identical workloads. Measure cold startup, warm first action, throughput, P50/P95/P99 latency, bytes read/transferred, source parses, cache hits by layer, lock wait, memory, and failure blast radius. Bazel's persistent and multiplex worker designs are relevant precedents; adopting their grouping idea does not certify Simple or Clang's provider implementations. [W07] [W08]

The promotion gate is **correctness first, then measured improvement**. If the grouped provider does not beat the qualified singleplex alternative on the target workload, keep the shared-resource interface and select the faster mode. Distribution and threads are policies over the same action model, not requirements that every action use both.

## References

[R02]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/src/app/build/targets/target_executor.spl "Simple named-target executor"
[R05]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/src/compiler/80.driver/cache/action_key.spl "Simple canonical action key and textual interface extraction; inspected lines 1–230"
[R11]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/doc/03_plan/compiler/build_system/targeted_build_interface_compat_minimal_bootstrap_2026-08-10.md "Simple targeted-build/interface plan; opening 130 lines inspected"
[W01]: https://clangd.llvm.org/design/threads "clangd: threads and request handling"
[W02]: https://clang.llvm.org/docs/PCHInternals.html "Clang: precompiled headers and modules internals"
[W03]: https://clang.llvm.org/docs/Modules.html "Clang: header modules"
[W04]: https://clang.llvm.org/docs/StandardCPlusPlusModules.html "Clang: standard C++ modules and dependency scanning"
[W05]: https://llvm.org/docs/ProgrammersManual.html#threads-and-llvm "LLVM Programmer’s Manual: threads and LLVMContext"
[W06]: https://clang.llvm.org/doxygen/DependencyScanningService_8h_source.html "Clang dependency-scanning service header"
[W07]: https://bazel.build/remote/multiplex "Bazel multiplex workers (documented as experimental)"
[W08]: https://bazel.build/remote/persistent "Bazel persistent workers"
[W09]: https://bazel.build/remote/caching "Bazel remote caching"
[W10]: https://bazel.build/basics/hermeticity "Bazel hermeticity"
[W11]: https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html "Rust compiler: incremental compilation in detail"
[W12]: https://ccache.dev/manual/latest.html "ccache manual; fetched version identifies itself as 4.14"
[W13]: https://man7.org/linux/man-pages/man2/mmap.2.html "Linux/POSIX mmap documentation"
[W14]: https://man7.org/linux/man-pages/man3/pthread_mutexattr_setrobust.3.html "POSIX/Linux robust mutex behavior"
[W15]: https://learn.microsoft.com/en-us/windows/win32/memory/creating-named-shared-memory "Microsoft: creating named shared memory"
[W16]: https://learn.microsoft.com/en-us/windows/win32/sync/interlocked-variable-access "Microsoft: interlocked variable access"
[W17]: https://www.kernel.org/doc/html/latest/admin-guide/cgroup-v2.html "Linux kernel: cgroup v2"
[W18]: https://learn.microsoft.com/en-us/windows/win32/procthread/job-objects "Microsoft: job objects"
[W26]: https://kubernetes.io/docs/concepts/scheduling-eviction/assign-pod-node/ "Kubernetes node selection and affinity"
