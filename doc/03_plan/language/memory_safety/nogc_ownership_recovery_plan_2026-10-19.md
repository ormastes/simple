# Simple No-GC Ownership Recovery and Memory-Exhaustion Prevention

**Implementation, architecture, formal-verification, and acceptance plan**  
**Date:** 2026-10-19, Asia/Seoul  
**Project:** `ormastes/simple`  
**Evidence snapshot:** `c8b4a86ab6876ecb825b4ea42b2c01d388b23a95`  
**Status:** Proposed implementation plan consolidating the conversation. No source changes, database migration, compiler execution, or new proof completion is claimed by this document.

> **Primary decision:** Restore and consistently enforce Simple's intended **no-GC, unique-owning-pointer default with strictly short, inferred borrowing**. Do not solve implementation defects by extending borrowing to longer ranges, adding general lifetime parameters, silently introducing reference counting, or enabling tracing garbage collection.
>
> **Compiler decision:** Use a **fused, streaming Parse → HIR → MIR → Object pipeline by default**, while retaining separately executable logical phases for debugging and verification. Share immutable artifacts through a long-lived build-runner session; keep mutable scratch private and bounded.

## Contents

1. [Decisions and scope](#1-decisions-and-scope)
2. [Repository evidence and corrections](#2-repository-evidence-and-corrections)
3. [Recover no-GC unique ownership and short borrowing](#3-recover-no-gc-unique-ownership-and-short-borrowing)
4. [Cyclic relationships and configurable detection](#4-cyclic-relationships-and-configurable-detection)
5. [Fused compiler with separable debugging phases](#5-fused-compiler-with-separable-debugging-phases)
6. [Phase-local memory and safe publication](#6-phase-local-memory-and-safe-publication)
7. [Build-runner immutable sharing and session lifecycle](#7-build-runner-immutable-sharing-and-session-lifecycle)
8. [XXH3 and BLAKE3 content-identity policy](#8-xxh3-and-blake3-content-identity-policy)
9. [Runtime, process, and scheduler hardening](#9-runtime-process-and-scheduler-hardening)
10. [Language-level changes: required, optional, and rejected](#10-language-level-changes-required-optional-and-rejected)
11. [Formal verification and implementation refinement](#11-formal-verification-and-implementation-refinement)
12. [Acceptance tests and protection against removal](#12-acceptance-tests-and-protection-against-removal)
13. [Memory and performance measurement](#13-memory-and-performance-measurement)
14. [Bug DB grouping and lifecycle integration](#14-bug-db-grouping-and-lifecycle-integration)
15. [Implementation work packages and rollout](#15-implementation-work-packages-and-rollout)
16. [Final release checklist](#16-final-release-checklist)
17. [Sources and evidence register](#17-sources-and-evidence-register)

---

## 1. Decisions and scope

### 1.1 Required defaults

The following decisions are requirements for this plan, not claims about complete implementation in the reviewed executable.

| Area | Required default | Explicit alternative or boundary |
|---|---|---|
| No-GC owning reference | One unique owner; deterministic cleanup | Explicit shared ownership, region ownership, or unsafe foreign contract |
| Ordinary temporary access | Short, inferred read or exclusive mutable borrow | Ownership transfer or handle resolution for longer relationships |
| Borrow lifetime | Remains inside the language's defined short boundary | **No automatic widening; no returned/stored long-lived borrows** |
| Ownership safety | Mandatory in every admitted execution route | Unsupported constructs are rejected, not executed unchecked |
| Shared reference counting | Never implicit for ordinary unique values or short borrows | Explicit non-atomic or atomic sharing when needed |
| Tracing or cyclic GC | Absent from no-GC mode | A separately selected managed runtime is outside this recovery |
| Compilation | Fused per ready unit, normally one parse of each exact parser input | Split/debug/replay modes and legitimate global semantic work |
| Compiler intermediate state | Worker-local, short-lived, directly handed between stages | Budgeted immutable publication or debug capture |
| Build-runner session | Default shared owner of immutable build data | Equivalent local session when compiling without the runner |
| Process isolation | Preserve existing isolated group-worker guarantees | Same-process worker groups only after concurrency qualification |
| Private trusted content lookup | XXH3-128, with collision-safe identity handling | Configurable algorithm through a versioned provider interface |
| Non-private/untrusted content identity | BLAKE3-256 | Existing mandatory external formats retain their required hashes |
| Cycle diagnostics | Bounded basic static shared-ownership checks | Deep analysis and targeted runtime detection are opt-in |
| Memory accounting | Lightweight owner/phase accounting and admission | Detailed allocation/edge tracing only in diagnostic profiles |
| Bug tracking | Existing SDN database plus root-cause relationships | Generated Markdown remains a view, not a competing authority |

### 1.2 What “recover” means

Treat an admitted no-GC route that loses an owner without executing required cleanup, silently copies a unique owner, or permits a borrow to escape its short boundary as a **semantic implementation defect**. A documented design does not establish that the executable implements it.

Recovery is not permission to change the observable semantics of every legacy class or struct without migration. Scalars and explicitly copyable value aggregates remain values. A heap-owning member makes implicit duplication of its ownership invalid unless the type defines a legitimate independent copy. Existing code that relies on accidental aliases must be migrated to explicit ownership, sharing, or handles—not made safe by silently extending borrows.

### 1.3 Scope of guarantees

Separate four questions:

1. **Memory safety:** Can an access use dead storage, race with unauthorized mutation, or release storage twice?
2. **Required reclamation:** Does a successfully constructed owner execute its promised cleanup on supported exit paths?
3. **Retention efficiency:** Does a valid owner retain more data, or retain it longer, than the algorithm needs?
4. **Resource containment:** Can aggregate memory use exceed the host or job's allowance?

Unique ownership primarily addresses the first two. Correctly owned ASTs, caches, or work queues can still consume all available memory. Rust permits safe-code memory leaks, including deliberate destructor suppression; Java can retain reachable objects indefinitely. Therefore, neither ownership nor GC replaces lifetime segmentation, bounded caching, and admission control. [E01][e01] [E02][e02] [E03][e03]

### 1.4 Implementation notation

Names such as `OwnershipFactsV1`, proposed test IDs, and configuration fields below describe **target interfaces**. They are not assertions that these names or command-line switches already exist. Reuse existing grammar, SDN encoders, type forms, and owner APIs wherever their contracts match. Introduce new syntax only after the grammar/compatibility gate in work package WP-01.

---

## 2. Repository evidence and corrections

### 2.1 Review boundary and Bug DB freshness

This document binds repository evidence to commit `c8b4a86ab6876ecb825b4ea42b2c01d388b23a95`. The connected branch response identifies an October 13, 2026 commit. The user reports additional Bug DB updates on October 19. This review does **not** independently establish that every such update is included in the accessible snapshot. [R00][r00]

The canonical `doc/08_tracking/bug/bug_db.sdn` returned an empty body through one connector action earlier in the conversation, but its content was subsequently accessible through GitHub's contents API at the pinned revision. The database is not empty merely because one retrieval failed. Nor does an old `Generated` line in `recent_bugs.md` establish the database's last update time. The mapping in Section 14 is a representative evidence-backed grouping, **not a complete October 19 row census**. [R01][r01] [R02][r02]

### 2.2 Findings that change the implementation plan

| Evidence | What it supports | What it does not support |
|---|---|---|
| Ownership-transfer bug record reports closed return, assignment, field, and collection move fixes, with mutation-tested fixtures | Preserve and extend existing repaired transfer paths | Reopening every historical move defect without a fresh reproduction |
| Interpreter ownership record documents a HIR route bypassing MIR-based checking | Audit mandatory checking across routes; avoid redundant full MIR solely for checking | A claim that the current producer has been executed and found defective here |
| Resource architecture is explicitly proposed and distinguishes resource types from legacy classes/structs | Reuse origin-neutral resource ownership and cleanup design | Proof that every plain class/reference already has the intended no-GC default |
| Semantic cache architecture lists existing owners and unqualified target contracts | Extend its snapshot, gateway, journal, pin, and summary boundaries | Claiming the whole daemon/semantic cache design is deployed |
| Grouped manager design uses isolated process groups and immutable parse cells | Preserve group isolation while adding real physical sharing | Replacing process isolation with threads without a state/thread-safety audit |
| Cold-inventory regression includes native before/after retention evidence | Per-entry scratch reclamation fixes that specific repeated workload | Full bootstrap memory/performance admission |

Sources: [R03][r03]–[R08][r08].

### 2.3 Corrections to historical attribution

The interpreter-worker report contains a later correction: the runtime immortal-allocation registry was not the dominant owner of that interpreter workload, and an earlier growth mechanism had already been repaired. Do not diagnose every seed/interpreter problem as “no GC means all values leak.” [R09][r09]

The Windows shard-budget report also records a later correction to an earlier Stage-2 memory interpretation: a Windows `/proc` unit conversion caused a 16-fold error. Preserve the old observation and its correction together; do not use the corrected number to size new worker budgets. [R10][r10]

A global-array OOM report ultimately attributes the runaway loop to mutation updating a different store from the one read by later global accesses. The final explanation is **inconsistent write-back**, not proof that a normal collection-size loop is inherently unsafe. Its existing fix and regression must remain covered. [R11][r11]

### 2.4 Evidence levels

Use separate evidence labels throughout implementation:

`proposed → source-reviewed → fixture-verified → integrated-producer-verified → target-qualified`

These are verification dimensions, not replacements for the existing bug lifecycle. A merged repair can remain unqualified for a particular target. A closed historical bug stays closed unless a new reproduction justifies a lifecycle change.

---

## 3. Recover no-GC unique ownership and short borrowing

### 3.1 Normative ownership contract

**OWN-01:** Each ordinary live no-GC owning reference has one active owning location. Assignment, return, closure transfer, field insertion, and container insertion transfer that ownership when the value is non-copyable.

**OWN-02:** Borrowing does not allocate a second owner or reference-count control block. Reading a unique owner through a short borrow does not transfer it.

**OWN-03:** A successfully initialized owned value receives exactly one required cleanup on supported terminating ownership paths, unless ownership was explicitly transferred or an explicitly permitted external ownership contract took responsibility.

**OWN-04:** No-GC does not promise destructors after process termination, an aborting panic, power failure, or an operating-system kill. Those events require process containment and external resource recovery. Cooperative cancellation, recoverable errors, and normal returns do require cleanup.

**OWN-05:** Safe default code has no implicit “forget owner” operation. Intentional externally managed lifetime or process-lifetime ownership must be explicit, auditable, and unavailable where the selected bounded-resource profile prohibits it.

**OWN-06:** A unique owner is not necessarily a heap allocation. Preserve inline scalar/aggregate layout, stack placement, caller-provided storage, and region-backed storage when valid.

### 3.2 Strictly short borrowing—no range expansion

Keep the existing intended short-borrow language boundary. During recovery, document precisely which expression/call-local scopes the grammar already permits and pin those rules with tests. Do not widen those scopes as an escape-analysis convenience.

A borrow may be forwarded through synchronous nested calls only within its originating short boundary. It must not be returned to create a longer-lived relationship, stored in a field/global/container, captured by an escaping closure, retained in a cache, or carried across a suspension or asynchronous submission.

| Operation involving a borrow | Required result |
|---|---|
| Read through an ordinary non-retaining call | Accept; no owner copy |
| Mutate through an exclusive short call | Accept when alias/effect rules permit |
| Finish last access before the short boundary ends | Borrow may end earlier; never later |
| Return or store the borrowed address/view | Reject |
| Capture in a nonescaping synchronous callback | Accept only with a checked nonescape contract |
| Capture in an escaping callback, task, or generator | Reject; require an owned value, shared owner, or handle |
| Keep a view across `await`, `yield`, or GPU/NIC submission | Reject; require an owned transfer or explicit owned pin token |
| Move/drop the owner while a short borrow is active | Reject |
| Reentrant callback invalidates the borrowed object | Reject or use a checked owner protocol that prevents invalidation |
| Resolve a stable handle during a later call | Accept as a **new short borrow**, not continuation of an earlier one |

A long-lived **owned lease or pin token** is not a long borrow. The token owns the permission that keeps storage available. Each access through it still uses a short checked view. This distinction allows asynchronous I/O and session-wide sharing without changing the borrow model.

### 3.3 Function and method contracts

Ordinary read-only receivers should borrow briefly instead of cloning the receiver. This is a semantic calling convention, not an optimization that assumes a retaining method is non-retaining.

Use compiler-known parameter effects such as `read-short`, `mutate-short`, `consume`, and `share-explicit` in typed metadata. These are semantic categories; this plan does not require new keywords. Definitions establish their contracts; imported summaries and FFI bindings carry equivalent trusted/checked metadata. Unknown foreign retention cannot be inferred away.

A method that consumes or retains an owner must be represented differently from a non-retaining inspector. Reject ambiguous unsafe behavior or require an explicit transfer. Do not introduce a lifetime variable to make the borrow escape.

### 3.4 Owner state machine and control-flow handling

For each owning place or independently movable field, maintain a state such as:

```text
uninitialized --construct succeeds--> live
live          --move---------------> moved
live          --required drop------> dropped
moved/dropped --initialize----------> live
```

Borrow information is associated with the live state and its short scope. Merges use actual control-flow successors and predecessors—not source order or the order of blocks in an array.

The checker must model partial moves, conditional initialization, loops, early returns, error propagation, and reinitialization. A move on a branch that cannot reach a later use must not cause a false rejection on the surviving branch. Conversely, a loop or merge must not resurrect a moved owner. The historical move-site report makes CFG-sensitive positive controls particularly important. [R03][r03]

Generate cleanup from live-on-exit facts. Insert drop flags only where conditional initialization/moves require them; eliminate flags proven constant. Do not move externally observable cleanup from a specified ownership boundary to an earlier last-use point merely to lower memory usage.

### 3.5 Containers, replacement, and failed operations

Cover all ownership transfers, not just `val b = a`:

- Return, explicit and implicit tail return.
- Assignment to local, field, optional, tuple, enum, array, map, or pool slot.
- Container insertion, replacement, extraction, removal, drain, and clear.
- Closure/task capture, argument passing, and resource wrapper construction.

A fallible insertion must either commit the move or leave/return the original owner according to one documented API contract. It cannot fail after destroying the only owner invisibly. Evaluate replacement values before discarding the old destination where necessary to preserve self-referential expression semantics, then commit and clean up in a defined order.

A container clear releases owned elements; retaining capacity does not retain their live object graphs. Capacity is tracked separately from live payload. Shared/COW value containers must not silently detach on every field update because the implementation manufactured a temporary alias.

### 3.6 Exactly-once cleanup and foreign resources

Use one ownership abstraction for memory, files, locks, sockets, GPU buffers, DMA registrations, and SFFI handles. The resource's origin is not a second ownership language. Reuse the existing resource architecture where applicable. [R05][r05]

Construction failure cleans up initialized members only. Recoverable exits follow generated cleanup edges. A destructor must not need a new allocation merely to record that it freed something. Fallible operations such as flushing persistent data need an explicit checked close/commit API; an automatic destructor cannot silently promise successful durable I/O.

At FFI boundaries, validate invalid-handle sentinels, ownership transfer, retain/release policy, alignment, and extent. Never infer ownership solely because an integer looks like a pointer. Asynchronous foreign calls require owned in-flight state, not a short borrow that happens to survive a test.

### 3.7 One mandatory checker across execution routes

Build a compact, target-independent ownership fact graph during typed HIR construction, or adapt an existing equivalent representation. A proposed `OwnershipFactsV1` contains owning places, moves, uses, short-borrow scopes, cleanup edges, and call effects. The interpreter and native paths consume the same semantics.

Do not make the interpreter build an entire redundant target MIR solely to discover use-after-move. Native MIR lowering must preserve the already-checked facts and verify its own transformations. Required ownership checking is always on for admitted no-GC execution; expensive escape optimization and cycle analysis remain optional.

Existing MIR ownership logic should be reused where sound. This is a factoring and coverage repair, not a second independent checker with different rules. The interpreter bypass record explains why simply adding a general MIR pass is not an adequate performance plan. [R04][r04]

### 3.8 Compatibility and bootstrap recovery

Bind ownership semantics to the grammar/semantic version used by the producer and artifact cache. Old unchecked artifacts cannot be silently reused under the recovered contract. Reject incompatible proof/ownership metadata and rebuild affected units.

Provide diagnostics for code relying on accidental copies or persistent aliases, including a replacement strategy: move the owner, use explicit sharing, or use a pool/session handle resolved briefly. Compatibility mode may support source migration, but it cannot label unchecked execution as conforming no-GC production behavior.

Acceptance must inspect actual emitted cleanup and execute it under each relevant runtime provider. Passing a parser or hand-built HIR test alone does not establish a working no-GC default.


## 4. Cyclic relationships and configurable detection

### 4.1 Ownership cycles are not ordinary graph cycles

A compiler may contain a cyclic call graph, mutually recursive types, parent links, or control-flow backedges without cyclic ownership. Make a pool/region/session own the nodes; store non-owning IDs on edges. Destroying the owner reclaims the nodes regardless of graph connectivity.

Explicit shared RC/atomic RC owners are different. Strong edges can keep each other alive after outside owners disappear. Weak links avoid adding a strong owner, but need their appropriate upgrade/validation protocol. Rust documents this distinction for `Rc`/`Weak`. [E01][e01]

**Correction to an earlier simplification:** “one incoming owning edge per node” alone does not prove acyclicity; a directed ring satisfies that condition. The unique-owned core must additionally preserve rooted, well-founded ownership and prohibit moves that place an owner into its own owned descendant. Short-borrow exclusion and place-overlap rules should establish this for normal safe operations. An unsupported indirect transfer is rejected or routed through an explicitly checked ownership API—not justified by indegree alone.

The graph data structure remains unrestricted when its edges are non-owning handles. No default runtime SCC traversal is needed for those edges.

### 4.2 Recommended representations

| Relationship | Representation | Reclamation rule |
|---|---|---|
| Tree children | Unique owned children | Owner cleanup releases children |
| Persistent parent/back link | Generational pool handle or another explicit non-owning identity | Resolve briefly; failed resolution is explicit |
| AST/HIR/MIR graph | Region-owned nodes with stable local IDs | Release region after consumers finish |
| Cross-module semantic edge | Immutable artifact ID and node ID | Session/cache lifetime and active leases |
| Shared runtime object | Explicit RC or atomic RC | Last strong owner releases payload |
| Weak RC relationship | Weak control-block reference | Upgrade returns failure if payload has expired |
| Temporary arbitrary cyclic graph | Explicit graph/arena owner | Bulk storage release plus required resource cleanup |

Do not describe a weak RC pointer as free metadata on a uniquely owned object. A weak-reference control block has a cost; use pool handles when that is the intended representation. Generation wrap, slot reuse, owner identity, and bounds must be checked. Retire a slot or widen the generation rather than silently accepting an old handle after wrap.

### 4.3 Cycle-check policy

These mode names are proposed configuration values, not claims about current CLI support.

| Optional diagnostic mode | Behavior | Where it runs | Effect when disabled |
|---|---|---|---|
| `basic` | Bounded local checks for evident shared strong self-links and simple cycles | Normal compilation; default | No change to required ownership checking |
| `deep` | Budgeted interprocedural graph construction, SCCs, and retention reasoning | Analysis/CI profile | No release runtime edge tracking |
| `runtime` | Explicitly enabled ownership-edge instrumentation and checkpoint diagnosis | Targeted debug workload | Instrumentation omitted from ordinary release builds |
| `off` | Disable optional cycle warnings | Explicit user configuration | **Unique/move/drop/short-borrow safety remains mandatory** |

Runtime detection does not collect cycles, decrement arbitrary owners, or modify program semantics. A cycle is not by itself a leak: it may have legitimate external owners. Report `strong-cycle-risk`, `unreachable-cycle-with-complete-evidence`, or `analysis-incomplete` separately. Sampling, untracked FFI edges, missing roots, and concurrent mutation cannot produce a proof of leak freedom.

Do not enumerate every possible cycle; that can itself explode. Build bounded graphs and report representative SCCs. Graph traversal is linear in a completed graph's vertices and edges, but constructing an accurate interprocedural graph can be much more expensive. Every diagnostic owner therefore has memory, node, edge, and time limits. Exhausting them returns an explicit incomplete result.

### 4.4 No longer borrowing as a cycle workaround

A parent link stored in a child is not converted into a long borrow. Use a handle or explicit weak/shared relationship. The handle's later lookup creates a fresh short view. This preserves the language's short-borrow model rather than importing a general lifetime system to support graphs.

---

## 5. Fused compiler with separable debugging phases

### 5.1 What “one pass by default” means

For normal cold compilation, parse each exact source/parser-configuration snapshot once. For each semantically ready unit, run the stages in one fused worker continuation:

```text
acquire immutable inputs
    → parse or verified parse-cache hit
    → publish necessary declaration surface
    → typed HIR + mandatory ownership facts
    → MIR + required validation/optimization
    → object/SMF contribution
    → release private unit scratch
```

The design removes unnecessary **whole-program barriers, intermediate copies, and serialization**. It does not claim the compiler performs only one traversal in total. Name resolution, typing, ownership validation, optimization, generic specialization, and linking remain real work.

Object emission can contain legitimate relocations to declared symbols. It cannot replace unresolved layouts, unknown ownership effects, or failed semantic checks with fabricated stubs. Existing no-stub and complete-SCC admission rules remain intact. [R07][r07]

### 5.2 One set of stages, multiple execution policies

Use common stage APIs and one implementation of each transform. Debug execution changes scheduling and artifact capture, not language semantics.

| Policy | Stage execution | Intermediate retention | Intended use |
|---|---|---|---|
| `fused` | Direct calls/continuations within a worker | Minimum required live state | Default production compilation |
| `split` | Run explicitly selected stage boundaries | Verified stage artifacts | Isolate a parser/lowering/backend defect |
| `checkpoint` | Fused with selected unit/stage captures | Bounded capture store | Debugging a reproducible failure |
| `replay` | Load an admitted stage artifact and continue | Needed artifact plus new scratch | Reproduce a downstream failure without upstream work |
| `analysis` | Add bounded deeper checks and profiling | Explicit larger diagnostic budget | CI, proof support, performance analysis |

A “stop after HIR” result is a successful HIR diagnostic result, not a completed executable. Replay validates producer/semantic version, snapshot, dependency read set, schema, target where applicable, ownership state, and artifact completeness.

Prefer a small fixed stage interface that the optimizer can inline or specialize. Do not impose a heap-allocated future, dynamic plugin lookup, or IPC transaction between every internal stage merely to retain the ability to debug them separately.

### 5.3 Declaration readiness, SCCs, and global work

A fused worker needs stable semantic authority. Establish readiness using compact declarations, TLDR/module surfaces, required layout/effect facts, and explicit dependency edges.

On a cold build without valid summaries, the one parser produces declarations and bounded immutable body syntax/capsules together. Bodies waiting for declaration resolution can be queued or spilled in their parsed form. Later loading/decoding a body capsule is not a second source parse. A diagnostic/recovery policy that actually reparses must report that counter separately.

For mutually dependent declarations, resolve the necessary SCC collectively, then schedule its bodies. Do not publish a partially successful SCC as a fully admitted group. Demand-driven generic instantiations use canonical work keys and cycle/size budgets; changing an upstream type/layout fact invalidates dependent work rather than mutating published HIR in place.

Whole-program checks and selected optimizations use compact summaries and explicit barriers. For example, ThinLTO separates a summary-based whole-program step from parallel backend work; the relevant lesson is to isolate global information requirements instead of retaining every rich frontend object. This does not prescribe replacing Simple's backend with LLVM. [E05][e05]

### 5.4 Sharing at each stage

| Data | Share by default? | Conditions |
|---|---|---|
| Frozen source bytes and source identity | Yes | Same immutable snapshot object |
| Public declarations/TLDR and immutable type/name identities | Yes | Complete relevant semantic identity |
| Parsed body/AST | When needed by multiple consumers or deferred work | Frozen independent storage, no mutable worker pointers |
| HIR | Selected immutable summaries/bodies | Ownership/effect/layout/read-set identity matches |
| MIR | Selected frozen module/function capsules | Optimization and target assumptions match |
| Object code | Yes through artifact store | Exact backend/target/ABI/toolchain and action identity |
| Parser stacks, symbol mutation workspace, optimization tables | No | Worker owns mutable scratch |

Sharing an artifact does not require persisting it to disk on every use. Direct same-process handoff is preferred for single-consumer cold work. Freeze and publish at an actual reuse, deferral, process, or persistence boundary.

### 5.5 Debugging without default retention

When capture is disabled, there should be no capture-buffer allocation, serialization, or disk write attributable to debugging. Verify this in emitted-code/counter tests instead of assuming it from a flag.

A selected capture includes source/snapshot identity, stage version, unit ID, dependency read set, target metadata, ownership verification result, and a bounded diagnostic record. Capturing rich graphs can increase memory substantially; use streaming encoding or explicit spill and record its cost.

Do not retain the preceding stage solely because debug tooling might eventually ask for it. In split/replay mode, stable IDs and source spans must survive serialization without process-local pointers or ambiguous symbol IDs.

---

## 6. Phase-local memory and safe publication

### 6.1 Lifetime map

| Storage class | Owner and lifetime | Release boundary |
|---|---|---|
| Request arguments and control messages | One admitted request | Request finish/cancel |
| Source-file read/canonicalization/hash scratch | One inventory entry | Entry validation/publication completes |
| Parse scratch | One parse unit | Parse finish/error |
| Mutable AST/HIR/MIR working state | Current function/module or required SCC | Last required consumer |
| Frozen semantic data | Session/cache owner | No active pin and eviction policy permits |
| Backend scratch and temporary buffers | One emission unit | Object finalization/error |
| Child output parsing | One result/event window | Summary emitted |
| Debug capture | Diagnostic owner with separate quota | Capture expiry/session close |

Reuse buffers with a measured capacity policy. A single exceptionally large module must not permanently inflate every reusable worker arena. After a high-water event, trim oversized slabs at a safe boundary; preserve small normal-workload slabs for throughput.

### 6.2 Arena rules

A region/arena is an explicit owner, not a substitute for ownership. Distinguish:

- **Dropless storage:** nodes contain only data that needs no individual external cleanup; bulk release is sufficient.
- **Resource-bearing storage:** nodes own files, locks, reference-counted members, external allocations, or device handles; region shutdown executes the required cleanup before reclaiming backing storage.

Nested regions need explicit owner tokens. A failed scope-begin cannot be treated as successful ownership, and an inner caller must not end a caller-owned outer scope. Cancellation and error paths release only the scopes they acquired.

Prefer slab adoption or moving independent owned results over walking every object to “promote” it. When graph promotion is necessary, include reachable owned backing storage and required metadata; a top-level reference alone is insufficient. Never traverse all previously retained inventory entries again for each new file.

Rustc's arenas and interning are useful implementation references, but the intended lifetime boundaries here are Simple's own module/function/session boundaries. [E04][e04]

### 6.3 Publication protocol

```text
private mutable builder
    → validate complete result and ownership closure
    → freeze independent representation
    → acquire publication reservation
    → publish immutable result atomically
    → transfer storage ownership / retain explicit dependency leases
    → release private scratch
```

An immutable artifact may refer to another immutable artifact through an admitted ID/lease. It must not retain a pointer into a worker arena. A generation-bound node ID detects reuse, but detection does not replace correct ownership.

A failed publication leaves either a private owned result that can be retried or a cleanly discarded result. It must not expose a half-initialized shared object. A losing concurrent publisher releases its own storage; it cannot destroy the winner's admitted artifact.

### 6.4 Bounded queues and backpressure

Bound queued units by **bytes and semantic readiness**, not just item count. A queue of ten enormous HIR capsules is not small merely because its length is ten.

Prioritize draining downstream work when intermediate memory grows. Reserve a minimum path to finish at least one ready unit, preventing all memory from being consumed by queued upstream work. Spill parsed/frozen artifacts when justified; fail clearly when required live state alone exceeds the cap.

The target is:

```text
live memory = required semantic state
            + admitted reusable cache
            + bounded active-unit scratch
            + bounded queues/diagnostics
            + runtime and safety headroom
```

It is not constant memory for an arbitrarily large program. Necessary exported metadata, specialization work, and output state can legitimately grow with the input.

---

## 7. Build-runner immutable sharing and session lifecycle

### 7.1 Default session authority

Use a long-lived `BuildRunnerSession` as the common immutable-data owner during interactive development or a batch build. It owns snapshot publication, cache admission, worker reservations, and cleanup. Reuse the existing semantic cache contracts rather than adding a competing daemon/database. [R06][r06]

```text
BuildRunnerSession
    SnapshotOwner          frozen source identities and bytes
    ArtifactGateway        verified lookup and publication facade
    ImmutableStore         bounded resident source/syntax/semantic artifacts
    ActionCoordinator      single-flight work and dependency state
    ResourceManager        memory/commit/device reservations and backpressure
    WorkerGroups           isolated groups; private mutable unit scratch
    PersistentCAS          optional immutable durable storage
    RootJournal            admitted root/action mappings
    EvidenceSink           bounded progress, failure, and resource receipts
```

The compiler still works without a test runner, IDE, or external daemon. Standalone compilation creates an equivalent local session using the same API and correctness rules. A crashed cache service is not permission to use unverified data or disable snapshot validation.

### 7.2 Unique session owner, shared reads, short access

The session uniquely owns shared storage. A worker owns a small **lease token** identifying a pinned artifact generation. It does not acquire another unique owner of the artifact payload.

For each operation the worker resolves the lease to a short immutable view. The short view cannot be stored or returned beyond its allowed boundary. Asynchronous tasks keep owned lease tokens, not borrowed views. On completion they release tokens; the cache may retain unpinned artifacts within its quota.

This gives session-long sharing without session-long language borrows or per-node atomic reference counts. Charge synchronization to lease acquisition/release or chunk transitions, not to every AST edge traversal.

### 7.3 Physical sharing across processes

Separate processes cannot exchange ordinary heap pointers safely. Share frozen, relocatable byte layouts or file-backed artifacts instead. Use fixed-width checked offsets/indices, explicit layout versions, alignment, and defined byte order. Validate counts, lengths, arithmetic, and transitive artifact references before a consumer trusts the representation.

A common cache directory alone provides logical reuse, not necessarily physical sharing. If each process decodes the entire AST/HIR into a private heap, duplication remains. Add read-only views over the frozen representation and decode only the mutable working subset a worker actually needs.

Platform adapters provide mappings and lifetime enforcement. File-backed immutable mappings can be mapped on demand; shared bytes need not all be eagerly resident. Mutable source files must never stand in for the frozen snapshot merely because their paths match.

### 7.4 Processes versus threads

The reviewed grouped manager architecture intentionally uses isolated compiler groups and private mutable output/cache state. Preserve those safety and failure-isolation properties. [R07][r07]

A qualified group may contain multiple threads/fibers once its parser globals, symbol identity owners, runtime allocation state, and phase workspaces are proven group-safe. Threads can directly share frozen structures and avoid IPC; they do not repair an unbounded cache or make mutable global frontend state safe.

Keep separate groups for crash-prone providers, incompatible runtime state, external tools, and explicit isolation policies. Fibers reduce some scheduling costs but can retain large suspended frames; cap in-flight fibers and charge their live state. Do not use process restarts as the only permanent reclamation mechanism, but retain bounded worker recycling as containment for unqualified providers.

### 7.5 Session duration is not retention duration

A long-lived session has multiple source generations. New edits create a new snapshot; active work finishes against its pinned old snapshot. Unused old generations become reclaimable when their work, artifact dependencies, and reader pins end.

Separate cache lifetimes:

| Tier | Contents | Policy |
|---|---|---|
| Worker-local | Mutable scratch and tiny hot lookup state | Reset at unit/function boundaries |
| Session RAM | Hot immutable artifacts and required surfaces | Quota, active pins, bounded eviction metadata |
| Local persistent CAS | Reusable frozen syntax/semantic/object outputs | Capacity/age policy with admitted roots and leases |
| Remote CAS | Compatible verified artifacts | Explicit trust and publication policy |

Session shutdown cancels or completes owned work, reaps managed processes, retires publication attempts, waits for actual reader quiescence, and then releases memory. Lease timeout alone cannot justify unmapping storage still used by a live local reader. Revoke access through a supported protocol or terminate the owning managed worker before reclaiming its pins.

### 7.6 Source inventory and editing integration

SCV/Git supplies version and source authority; it is not the mutable artifact cache. Resolve aliases to one physical source identity while preserving semantic/logical names and diagnostic presentation paths.

SPipe/IDE editing logs are incremental hints. The snapshot service verifies byte identity and dependency/resolution changes; an edit log or unchanged timestamp does not prove cache validity. Capture positive and negative resolution witnesses so newly added modules, changed conditional imports, generated files, or aliases invalidate the right work.

Read an entry through one authorized handle, bound its canonicalization/hash/validation scratch, publish the retained row, and release entry scratch. Avoid a second cold inventory in child workers. Do not exclude every ignored directory without proving the source-authority contract still covers all relevant inputs.

### 7.7 Single-flight and crash-safe publication

For one exact semantic action, elect one active producer with an owner generation. Other consumers subscribe rather than each rebuilding the same dependency.

```text
absent → claimed(generation) → producing → validated → admitted
                              ↘ failed/cancelled → recoverable terminal state
```

A heartbeat renews an owner's claim; it is not a success receipt. Recovery verifies the old producer is no longer able to publish before admitting a replacement generation. Writes remain private until validated publication; a failure cannot create a success cache hit. Keep result/diagnostic records separate from reusable artifact authority.

Use the existing journal-before-projection design: an admitted root mapping is durable authority; a database index is rebuildable metadata. Missing/corrupt cache data produces a verified miss/rebuild or an explicit failure, never fabricated content. [R06][r06]


## 8. XXH3 and BLAKE3 content-identity policy

### 8.1 Trust policy—not “cryptographic hashing everywhere”

Respect the requested performance policy: **XXH3-128 by default inside an explicitly trusted private environment; BLAKE3-256 by default at non-private or untrusted boundaries.** XXH3 is non-cryptographic; BLAKE3 is a cryptographic hash. Neither a hash match nor a signature alone proves semantic compatibility. [E06][e06] [E07][e07]

“Private” must describe access and producer trust, not merely an intranet address or private repository flag. A local cache writable by untrusted jobs or ingesting untrusted prebuilt artifacts is not automatically trusted. Unknown trust defaults to the strong boundary policy. Do not downgrade a configured boundary because a file was copied onto local disk.

| Use | Default | Additional requirement |
|---|---|---|
| Hash-table bucket selection | XXH3 | Compare actual keys |
| Private-session content lookup | XXH3-128 | Collision-disambiguated identity |
| Trusted private persistent CAS | XXH3-128 permitted/default under this policy | Immutable admission, canonical identity, collision handling and integrity checks |
| Remote or untrusted artifact admission | BLAKE3-256 | Bounded decoding, trusted action/producer policy |
| Release/security-significant identity | Strong policy, normally BLAKE3-256 | Authentication/provenance where required |
| Existing external protocol or manifest | Protocol-required algorithm | Do not break compatibility to enforce a new default |

The algorithm is replaceable through one provider interface; do not embed a BLAKE3 implementation in each subsystem. CPU/SIMD dispatch and pure-Simple/external-provider selection must preserve canonical outputs and test vectors. Measure hashing on the actual input sizes and target ISA rather than assuming a universal speed ratio.

### 8.2 Collision correctness in private mode

Trusted inputs can still collide accidentally. Therefore **length plus an XXH3 digest is not exact equality**.

Treat the digest as a lookup index. During deduplication/admission, compare canonical descriptors and, for distinct content candidates, the actual bytes or an already established exact immutable identity. Store colliding candidates in separate bucket entries; never overwrite or alias them solely by hash. All leaf references in an action must be disambiguated, not merely the action's top-level hash.

After exact identity and immutability are established, repeated same-session consumers can reuse the admitted object identity without re-comparing its entire payload on every access. Equality checks cost O(bytes compared); account for this work and amortize it at admission. Do not describe collision-safe private hashing as mathematically free.

A persisted collision discriminator is a private store detail, not a portable trust credential. When exporting an artifact, compute the required strong identity over canonical bytes and bind it to the manifest. Hash agility records algorithm, digest width, domain, schema, and encoding version. A private XXH3 object must never masquerade as a BLAKE3 object with a different-length field.

### 8.3 Separate identities by semantic role

| Identity | Inputs that matter |
|---|---|
| Content reference | Exact bytes, content-domain/schema, hash policy |
| Parse action | Content, grammar/parser/codec identity, exact parser preprocessing and feature decisions, semantic logical path if required |
| HIR/typed action | Parse result, imported surfaces, resolution witnesses, type/effect/ownership rules, macros/aspects and consumed compile-time inputs |
| MIR action | Typed input, layouts/ABI, specialization decisions, relevant target facts and pass pipeline |
| Object action | MIR, backend/toolchain/runtime ABI, CPU/GPU target features, optimization/debug mode, code-generation inputs |
| Link action | Ordered object/library inputs, linker identity/options, runtime/provider and export/initialization policy |

Do not put every host property into every key; that destroys safe reuse. Conversely, source-byte equality alone does not justify sharing HIR specialized against different imports, entry roles, aspects, or target assumptions. The repository's closed-batch review explicitly warns against drawing that conclusion from repeated source paths. [R25][r25]

Physical paths, branch names, mtime, and mutable database row numbers are not portable content identity. Include logical path when it changes language behavior; retain presentation paths separately for diagnostics. Preserve negative dependency witnesses for previously absent imports or configuration branches.

### 8.4 Streaming hashing and bounded validation

Hash source bytes as the snapshot owner reads them. Reuse the admitted digest; do not rescan the entire source tree at every child startup. When both private and export identities are needed, compute the second digest at the boundary or in the same read when policy predicts export—do not require both for every private action.

Check integer overflow before calculating offsets, allocation sizes, or decoded extents. Cap decompressed sizes and node counts before allocating. Cryptographic integrity does not make a compressed payload safe to expand without limits. Verified immutable artifacts may cache their validation result within a pinned generation.

Corrupt cells are quarantined with bounded evidence. Repair never means accepting a weaker hash, silently dropping a dependency, or resetting provenance to an arbitrary newer source snapshot.

---

## 9. Runtime, process, and scheduler hardening

### 9.1 Hidden copies and allocator registries

The readonly-receiver and unchecked-allocation reports identify distinct hazards: allocating an aggregate for a getter can exhaust allocation bookkeeping, and unchecked allocation failure can turn exhaustion into memory corruption. Increasing registry capacity alone addresses neither unwanted copies nor absent reclamation. [R14][r14] [R15][r15]

Required implementation rules:

| Mechanism | Required behavior | Cost control |
|---|---|---|
| Read-only non-retaining receiver | No unnecessary aggregate heap copy | Use proven short-borrow ABI |
| Genuine value copy | Preserve independent-value semantics | Inline/memcpy/explicit clone as appropriate |
| Allocation registry | Reuse retired slots; bound metadata to live demand and controlled spare capacity | Avoid a global contended lock per ordinary field read |
| Allocation failure | Check before any store/dereference; propagate or fail-stop coherently | Cold failure path; no diagnostic allocation recursion |
| Container capacity growth | Checked arithmetic and bounded demand | Reserve when justified; do not reserve an unbounded prediction |
| Reusable scratch | Clear live members and reuse normal capacity | Trim exceptional high-water slabs safely |
| Error/diagnostic collection | Stream; retain a bounded summary and bounded excerpts | No repeated full-output split/copy |

Do not change a value type into an identity class simply to avoid copies without preserving alias semantics. Do not blanket-borrow a receiver that returns itself, stores itself, or calls unknown retaining code. The short-borrow contract is the proof boundary.

Detailed allocation registries and debug guards may be configurable where they are instrumentation only. Required validity/lifetime checks cannot be disabled just because they are expensive in a defective representation. First replace the representation or remove redundant checks with proof.

### 9.2 Process lifetime and orphan prevention

A wait timeout is not proof that the child exited. The shard-child bug documents the resulting overlap between abandoned work and new compiler phases. [R16][r16]

The build runner must own a managed process tree before allowing the workload to run. It records start identity, task generation, resource reservation, and terminal reaping. On timeout/cancellation, stop publication rights, terminate the managed workload through its owner, reap descendants, close inherited handles, and release reservations only after ownership actually ends.

On Windows, Job Objects provide group management, termination, and limits; use an appropriate kill-on-close/assignment policy and verify nested-job/breakaway behavior rather than relying on executable-name matching. On Linux, use the admitted cgroup/process supervision owner, not just an RSS-polling shell that can die before its child. [E08][e08] [E09][e09]

No blanket `kill simple` operation: unrelated MCP, IDE, and other user sessions may use the same executable. Use process identity and managed task boundaries. A recorded PID alone is insufficient because it can be reused.

### 9.3 Memory-aware scheduling

Keep separate resource dimensions: resident/private memory estimates, shared physical residency, virtual address space, Windows commit headroom, OS job/cgroup charges, device memory, and pinned DMA memory. One “free RAM” number cannot substitute for all of them.

For planning, use a shared-once/private-per-worker estimate:

```text
estimated peak = manager private state
               + shared resident working-set allowance
               + sum(active worker private reservations)
               + queued-artifact and diagnostic allowance
               + runtime/OS safety headroom
```

Admit new work only when every enforced resource dimension has room. Propagate the smallest applicable declared limit through all nesting layers; a host-wide availability probe must not override a smaller parent job cap. If a needed measurement is unknown, use a conservative validated profile or refuse admission—not unlimited fanout.

Linux cgroup v2 distinguishes reclaim/throttling pressure (`memory.high`) from a hard limit (`memory.max`), and its charges are not simply a sum of process RSS. Model enforcement explicitly and retain kernel events for attribution. [E09][e09]

Avoid deadlock by reserving completion capacity for active units, limiting deferred bytes, and allowing downstream draining. Worker estimates are phase- and workload-sensitive. Learn from qualified receipts, but clamp outliers and never reduce hard containment because a short sample looked small.

### 9.4 Failure outcomes and diagnostic survival

Report separate outcomes: allocation failure, budget rejection, watchdog termination, OS OOM evidence, timeout, cancellation, compiler semantic error, crash, and unknown external termination. An exit code or signal alone is not definitive OOM evidence.

Record progress before each expensive boundary and emit durable bounded samples throughout execution. A telemetry summary written only during normal process shutdown is insufficient for an aborting allocation failure.

Use fixed or pre-reserved emergency reporting buffers. Log requested allocation bytes, phase/unit identity, current reservation, allocator live/backing bytes where available, producer identity, and last progress. Full heap/edge dumps are opt-in and have their own limits.

### 9.5 File handles, source authority, and OS/device resources

A file walker must bound simultaneously retained handles, not only the total entries it permits. Preserve same-handle read and source-authority validation while closing handles progressively; do not weaken race/symlink validation merely to reduce memory. [R17][r17]

GPU/NIC/NVMe work keeps owned completion state and explicit pins until completion or a proven cancellation/quiescence transition. Never free DMA-visible storage when only the host's short borrow ends. A pin is an owned resource obligation, not an expanded language borrow.

For bare-metal Simple OS, resource and pool budgets must be enforced by its own owners; desktop process containment is not available there. Hardware timeout/reset policies cannot be confused with successful cleanup or persistence.

---

## 10. Language-level changes: required, optional, and rejected

### 10.1 Required beyond repairing the default owner

Most useful additions are stronger semantics and shared compiler facts, not new grammar.

| Contract | Why it is needed | Language/API change |
|---|---|---|
| Consuming/non-retaining parameter effects | Inferred short borrows must not silently escape | Prefer existing capability metadata; expose explicit transfer where needed |
| Move-aware container operations | Ownership is frequently lost at insertion/removal/replacement | Library contracts and lowering/checker parity |
| Resource construction/cleanup protocol | Heap reclamation alone does not close files or release device pins | Extend existing resource/SFFI design |
| Checked handle-to-short-view resolution | Persistent graphs and session sharing need safe access | Library/pool type; no longer borrowing |
| Explicit thread/async transfer capability | Unique ownership alone does not prove a foreign resource can change threads | Use existing effects/capabilities or a narrow checked extension |
| Bounded/checked allocation arithmetic | Overflow can bypass a correct owner model | Runtime/container checks; normally no syntax change |

None of these implies universal atomic RC, per-pointer dynamic borrowing, or an automatically widened lifetime.

### 10.2 Optional diagnostics and optimization

Reuse shared HIR/MIR performance facts for hidden COW copies, repeated materialization, expensive by-value calls, redundant normalization, missing useful reserve, long-lived caches, and suspend-retained state. The existing compiler-performance requirements already organize many such rules; add coverage there rather than independent recursive walks per lint. [R19][r19]

Use low-cost local diagnostics by default. Interprocedural escape/resource bounds, symbolic complexity, and deep cycles belong in an analysis profile with explicit budgets. A safety check that is required for an accepted construct cannot be reclassified as an optional optimization.

Optional firmware/mission-critical memory contracts may describe no-allocation, initialization-only allocation, bounded pool, maximum in-flight work, or maximum live storage. They must distinguish a proved bound from an unknown bound. A runtime budget can enforce a limit when a static proof is unavailable, but that is a different evidence kind.

### 10.3 Explicitly rejected approaches

Do not introduce longer borrow scopes, generic lifetime annotations for persistent graphs, implicit sharing of unique values, mandatory tracing/cyclic GC, per-node atomic refcounts in the compiler graph, or a mandatory runtime cycle walk on mutation.

Do not claim memory/performance neutrality for all safety fixes. Cleanup costs real work, ownership checking costs compilation, handle resolution can cost a branch, and cache validation can read bytes. Design these costs at coarse ownership boundaries, eliminate redundancy, and measure them.

---

## 11. Formal verification and implementation refinement

### 11.1 Verification strategy

Prove a small ownership/short-borrow core and selected infrastructure protocols, then connect those models to actual compiler/runtime owners through refinement checks, native fixtures, and mutation tests. Do not label an abstract theorem as a proof of every backend or allocator.

A useful model state is:

```text
State = heap + owning_places + short_borrow_scopes + control_flow
      + region_owners + initialized_members + artifact_leases
      + task/publication_generations
```

Unique ownership uses rooted ownership invariants, not just an owner-count property. Borrow scopes are fixed by the short-borrow semantics; the solver is not allowed to enlarge them to discharge a proof.

### 11.2 Required proof obligations

| Proof ID | Obligation | Implementation boundary |
|---|---|---|
| FV-OWN-01 | Legal execution preserves one active unique owner and rooted ownership | Typed ownership events and move operations |
| FV-OWN-02 | Uses of moved/uninitialized/dropped places are rejected | CFG analysis and place projection |
| FV-BOR-01 | Every borrowed access is within its original short scope and live owner | HIR facts, call effects, runtime boundary |
| FV-BOR-02 | Exclusive borrowing prevents conflicting access/owner invalidation | Place overlap, reentrancy, mutation contracts |
| FV-DROP-01 | Cleanup is at most once; required initialized members are cleaned on supported exits | Drop elaboration and error/cancel edges |
| FV-MOVE-01 | Fallible transfer either commits one owner or preserves the documented original owner | Containers, replacement, SFFI transfer |
| FV-REG-01 | Region release cannot invalidate a surviving legal reference | Freeze/promotion/lease protocol |
| FV-HANDLE-01 | Reused slots cannot validate an old owner/generation handle | Pool allocator and resolver |
| FV-PIPE-01 | Fused/split schedules preserve defined results and cleanup order | Stage contracts and dependencies |
| FV-CACHE-01 | A hit implies exact admitted input identity and complete semantic dependencies | Action keys, canonical identity and lookup |
| FV-LEASE-01 | Eviction cannot race a valid active reader; expired producer cannot publish | Epoch/pin and task-generation state machines |
| FV-FAIL-01 | Failure leaves no published partial success and no unowned reservation | Publication, task teardown, recovery |

Model resource-failure transitions as well as success. Include finite bit widths, size arithmetic, generation wrap policy, and effectful destructor ordering where those matter. Proving unbounded mathematical integers is not enough for a 32-bit implementation.

### 11.3 Lean4 proof admission

Proof CI must build the actual theorem roots and audit their transitive assumptions. Lean's `#print axioms` can expose indirect `sorryAx` dependencies; axioms can also assert falsehoods, and native-evaluation proofs expand the trusted computing base. Pin tool versions and maintain an explicit reviewed axiom policy. [E10][e10]

Disallow `sorry`, `admit`, unreviewed axioms, or weakened theorem statements in admitted proof roots. Keep approved standard assumptions explicit. A theorem about a simplified allocation model must name excluded behavior—unsafe FFI, forced process termination, external device failure—not silently assume it away.

Existing cache/formal and ownership work should supply models when sound. New files are proposed only after locating the corresponding existing verification owner.

### 11.4 Bridge to production code

The compiler emits or internally exposes ownership events before/after lowering. A validator checks that generated cleanup and ownership transfers match the checked program. Every optimization declares whether it preserves these facts or requires revalidation.

For the interpreter, execute the common checked events through its actual environment/global/container paths. For native backends, run produced binaries against each linked runtime provider and check resource effects. Verify compiler-source, executable, runtime archive/provider, configuration, and fixture identities in the receipt.

Use exhaustive small-state model tests for branching/move/drop behavior and randomized CFG block ordering to catch accidental array-order semantics. Pair negative tests with valid exclusive-branch cases so a checker that rejects everything cannot pass.

### 11.5 Claims intentionally not made

This plan does not prove termination of arbitrary user programs, statically bound every allocation, collect all RC cycles, guarantee cleanup after forced termination, or establish whole-compiler correctness from a model proof. Each admitted result states its scope and remaining assumptions.


## 12. Acceptance tests and protection against removal

### 12.1 Acceptance is executable behavior, not test-file presence

Add proposed acceptance IDs to the existing SSpec/traceability system. Each row below requires a positive control, a rejecting/failing control where applicable, and an actual route-specific execution receipt. A test that constructs HIR manually is useful but cannot replace a source-to-execution acceptance test.

| Acceptance ID | Required scenario and oracle |
|---|---|
| AC-OWN-01 | Default no-GC owner is moved on non-copyable assignment; second use is rejected |
| AC-OWN-02 | Read-only and mutable short calls preserve the owner without hidden receiver allocation |
| AC-OWN-03 | Explicit/tail return, field, optional, enum, tuple, array, map, and push transfers emit and execute one owner transfer |
| AC-OWN-04 | Partial move, reinitialization, early-return branch, loop, and join cases behave correctly under block-order permutation |
| AC-OWN-05 | Valid mutually exclusive paths compile; deliberately conflicting paths do not |
| AC-BOR-01 | Returning/storing/caching a short borrow is rejected, even when a longer lifetime could theoretically make it safe |
| AC-BOR-02 | Escaping closure, task, suspension, and asynchronous device submission cannot retain a short borrowed view |
| AC-BOR-03 | Nested synchronous forwarding respects the original boundary; reentrant invalidation is prevented |
| AC-BOR-04 | Long-lived owned lease plus repeated fresh short views works without widening a borrow |
| AC-DROP-01 | Normal return, reassignment, scope end, error propagation, and cooperative cancellation clean each initialized owner exactly once |
| AC-DROP-02 | Partial construction failure destroys initialized members only, in the defined order |
| AC-DROP-03 | Observable resource cleanup order is unchanged by last-use optimization |
| AC-FAIL-01 | Inject failure at every relevant allocation/registration/publication step; no unchecked store or partial success |
| AC-CONT-01 | Fallible insertion and replacement preserve the documented owner on failure and commit it on success |
| AC-CONT-02 | Clear/remove/drain release owned elements without requiring capacity to shrink |
| AC-REG-01 | Inner scope cannot end an outer scope; failed begin does not confer scope ownership |
| AC-REG-02 | Frozen retained roots survive scratch release; intentionally retained scratch references are rejected/detected |
| AC-REG-03 | A resource-bearing arena runs required destructors; a dropless arena has no unnecessary per-node cleanup |
| AC-HANDLE-01 | Freed/reused/wrong-owner/out-of-range/wrapped-generation handles fail resolution |
| AC-CYCLE-01 | Region-owned cyclic graphs are valid and reclaimed with their owner |
| AC-CYCLE-02 | Obvious shared strong-cycle risk is diagnosed in basic mode; ordinary weak/handle backedges are not mislabeled |
| AC-CYCLE-03 | Deep/runtime budget exhaustion reports incomplete; runtime detection does not collect or mutate objects |
| AC-CYCLE-04 | `cycle_check=off` does not disable mandatory move/drop/short-borrow checks |
| AC-PIPE-01 | Fused and split produce equivalent semantics, errors, source locations, and required cleanup |
| AC-PIPE-02 | Cold default path parses each exact parser input once; decode/replay and legitimate recovery are separately counted |
| AC-PIPE-03 | Capture-off produces no debug checkpoint allocations/writes; targeted capture/replay remains functional |
| AC-PIPE-04 | Cyclic imports, trait/default bodies, generic instantiation, static conditions, and layout dependencies stay correct |
| AC-PIPE-05 | Failed or incomplete SCCs never become admitted executable/SMF success |
| AC-CACHE-01 | Concurrent equal actions have one admitted producer; subscribers reuse the same immutable result |
| AC-CACHE-02 | New edits do not change an in-flight snapshot; expired generations cannot publish |
| AC-CACHE-03 | Eviction waits for actual reader quiescence; service crash cannot leave writable published artifacts |
| AC-CACHE-04 | Changed imports, negative resolution, target, runtime ABI, grammar, aspects, or entry role invalidate the affected stage |
| AC-HASH-01 | Inject equal XXH3 digests for different bytes/actions; no false cache hit or overwrite occurs |
| AC-HASH-02 | Private-to-untrusted export uses the boundary's strong identity; algorithm/schema confusion is rejected |
| AC-HASH-03 | Scalar/SIMD/pure/external hashing providers match canonical vectors and streaming/chunk boundary results |
| AC-PROC-01 | Timeout, cancellation, parent death, worker crash, and spawn failure leave no surviving managed descendants or leaked reservations |
| AC-PROC-02 | PID reuse and unrelated `simple` processes cannot be mistaken for managed children |
| AC-BUDGET-01 | Parent/job limit reaches grandchildren; unknown measurements cannot enable unlimited worker fanout |
| AC-BUDGET-02 | Queue/fiber/output/device-pin budgets work independently of worker count |
| AC-METRIC-01 | Known allocations and process fixtures calibrate bytes/KiB/pages; missing metrics are unavailable, never zero |
| AC-METRIC-02 | Repeated equivalent units show bounded scratch after warmup; intentionally retained artifacts are separately attributed |
| AC-DB-01 | Group migration preserves every existing unrelated row/table and status; malformed/partial input causes no write |
| AC-GATE-01 | Zero executed tests, omitted mandatory backend, or missing proof root cannot report PASS |
| AC-GATE-02 | Removing/bypassing a checker, cleanup operation, or required test is detected by an independent gate |

### 12.2 Backend and runtime matrix

Cover the actual product execution routes: seed interpreter, self-hosted interpreter where distinct, JIT, native Cranelift, native LLVM, and every production runtime provider used by those routes. The matrix must distinguish compiler code generation from linked C/Rust/pure-Simple runtime behavior.

Add x86-64 and ARM64 host qualification, relevant Windows/Linux/macOS/FreeBSD adapters, and 32-bit/RISC-V targets where supported. GPU/VHDL/bare-metal routes run applicable ownership/storage tests, including host/device transfer; a CPU process fixture is not blindly required on a device backend.

An unsupported construct or route is explicitly rejected/classified. Do not skip it silently or count a source parse as runtime parity. Re-run the actual failing no-GC bootstrap route after the focused repair; a Rust-seed-only result does not qualify a pure-Simple producer.

### 12.3 Sabotage and mutation controls

A repair is protected only when the corresponding bad implementation is known to fail the gate. Use isolated temporary worktrees/builds, hard memory limits, and exact mutation identity. Never inject a runaway case into a shared unrestricted worker.

Mandatory mutation families include:

| Mutation | Gate that must fail |
|---|---|
| Bypass no-GC ownership checking on interpreter entry | Source-level invalid borrow/move corpus |
| Replace a required move with an owning copy | Transfer/event and actual cleanup tests |
| Remove a cleanup edge | Live-resource and exactly-once tests |
| Extend a borrow across a return/store/await | Short-boundary negative tests |
| Change CFG traversal to linear block order | Block-permutation and branch-positive tests |
| Omit per-file/phase scope end | Repeated owner-attributed scratch regression |
| Keep a timed-out shard running | Process-tree teardown and next-task admission test |
| Drop the enclosing resource cap | Nested worker-limit test |
| Force hash collisions or omit a semantic dependency | Collision/invalidation corpus |
| Return fabricated zero allocation counters | Counter calibration/independent resource test |
| Remove a mandatory acceptance row or workflow invocation | Coverage-manifest/wiring gate |
| Introduce a `sorry` dependency or weaken an admitted theorem contract | Proof-root and axiom/contract audit |

Tests may need a minimized failing fixture rather than replaying a full historical OOM. Retain the connection from that fixture to the real bug, and still require a bounded integration run for closure where the record demands it.

### 12.4 Preventing removal, bypass, and false-green coverage

Maintain a reviewed requirement-to-proof/test manifest using the existing SDN/traceability infrastructure. A rename updates identity mapping; it does not delete the obligation. Required IDs, assertions, routes, and result kinds are compared against a protected baseline independent of the change under test.

A gate must verify invocation and executed cardinality, not simply search for a function name in source. Required check statuses must be bound to the exact candidate. Attempts to weaken a threshold, delete a negative control, change the theorem statement, or replace execution with source inspection need explicit reviewed contract changes.

Local hooks should stay bounded: schema integrity, changed-contract mapping, focused owner tests, and wiring checks. Full Lean proofs, mutation tests, cross-host coverage, and larger memory regressions belong in required CI/release lanes. Do not put an expensive self-bootstrap on every commit.

Repository protection cannot make deletion impossible against an administrator authorized to change both code and policy. The implementable goal is to prevent **silent ordinary removal or bypass**, with an independent required-check policy and review boundary. This document does not claim those repository settings have been configured.

### 12.5 Failure reporting

Every gate records `PASS`, `FAIL`, `BLOCKED/UNAVAILABLE`, or `NOT_RUN` with a reason and evidence identity. Missing tools, failed compilation of the fixture, zero scenarios, or a timed-out reporter cannot become PASS. A diagnostic run under an exception remains outside normal release admission until the ordinary gate succeeds.

---

## 13. Memory and performance measurement

### 13.1 No unsupported percentages

The effects below are engineering expectations, not benchmark promises for the current Simple tree. No meaningful safety check is declared “free” without measuring its actual implementation.

| Mechanism | Expected memory effect | CPU/latency effect and risk | Default policy |
|---|---|---|---|
| Unique ownership and deterministic cleanup | Stops required-owner leakage | Cleanup work; usually avoids RC traffic | Required |
| Short non-retaining receiver ABI | Avoids temporary aggregate allocation | Usually less copying; checking has compile cost | Required semantics |
| Module/function regions | Bounds temporary live state | Cheap allocation/reuse; cleanup may traverse resource members | Default |
| Fused direct stage handoff | Avoids checkpoint copies and retained stage sets | Better locality; dependencies can stall units | Default |
| Session immutable sharing | Reduces duplicate source/surface payloads | Lease/validation cost; cache retention can grow | Default, quota-bound |
| Frozen process-shared views | Reduces actual private duplication | Mapping/page faults/offset access; format engineering | Use where beneficial |
| Per-unit serialization | Can enable spill/replay | Extra CPU, writes, and temporary buffers | Not universal |
| XXH3 private identity | Small digest/index state | Hashing plus collision-safe admission comparisons | Private trusted default |
| BLAKE3 boundary identity | Small strong digest state | Boundary hashing/verification | Untrusted default |
| Worker memory admission | Prevents aggregate oversubscription | May reduce parallelism when memory is scarce | Required |
| Basic cycle/lifetime diagnostics | Small bounded compile metadata | Nonzero compiler work | Basic checks default |
| Deep analysis/runtime edge tracking | Additional graph/trace memory | Potentially substantial | Opt-in |
| Proof/mutation CI | No application runtime footprint | Build/test infrastructure cost | Required appropriate CI tier |

### 13.2 A real narrow regression—not a whole-compiler claim

The cold-inventory record provides a useful example of attributable prevention. Its 50,000-call native workload reports the following values. They are historical fixture measurements, not results rerun for this document. [R08][r08]

| Measure | Baseline fixture | Scoped candidate fixture |
|---|---:|---:|
| Retained objects after workload | 950,009 | 9 initialization objects |
| Peak process RSS | 83,892 KiB | 4,960 KiB |
| Recorded elapsed time | 0.40 s | 0.33 s |

The record separately reports zero growth after warmup in its checked native fixture and preserved semantic/negative controls. These finite samples support that specific retention repair. They do not establish statistical speedup, full cold publication success, or Stage 3/4 memory admission.

### 13.3 Required metrics and attribution

Record by owner and phase:

- Live payload bytes, live backing-buffer bytes, region reserved bytes, registry capacity/tombstones, and live resource counts.
- Source reads/bytes, raw parse count, decode count, parse/HIR/MIR/object hits/misses, single-flight waits, materialized bytes, and bytes copied.
- Private/resident/committed memory where available, process-tree enforcement charge, page faults, device memory and pinned in-flight bytes.
- Phase duration, end-to-end duration, queue delay, active worker/fiber count, cancellation cleanup duration, and output identity.

Peak RSS does not prove absence of a leak, and live object count is not live bytes. An allocator may retain free slabs after objects die. Separate payload reclamation from capacity retention and OS page residency. The existing HIR report documents why mismatched providers/counters can invalidate a claimed ownership-byte measurement. [R23][r23]

Shared mappings can appear in several processes' RSS; summing those values can double-count physical memory. Linux `smaps` exposes proportional set size (PSS), which helps distinguish shared/private attribution. Still record the actual enforcement metric, because PSS and a cgroup charge are not interchangeable. [E11][e11]

Calibrate each OS provider with a known workload, native API units, and an independent observation. Never assume Windows MSYS `/proc`, Linux `/proc`, and macOS timing tools report identical units or semantics. Preserve raw values and their unit tags.

### 13.4 Workload matrix

Use fixed producer/input pairs and separate cold, warm, and repeated-session runs:

| Workload | Main purpose |
|---|---|
| Tiny entry with explicit source bounds and with ordinary entry discovery | Detect whole-repository startup/materialization amplification |
| Repeated identical module/function workload | Detect residual scratch and runtime registry growth |
| Increasing independent module counts with controlled exported surface size | Separate necessary metadata growth from temporary retention |
| Large SCC/generic/layout fixture | Validate bounded deferral and legitimate global work |
| Output-heavy repeated test execution | Detect parent-side diagnostic/result accumulation |
| Concurrent equal-source/equal-action workers | Measure real deduplication and single-flight behavior |
| Concurrent equal-source/different-semantic-action workers | Ensure sharing does not create false cache hits |
| Long session with repeated edits and old snapshots | Detect leaked generations, leases, and invalidation state |
| Forced cancellation/crash/timeout/failure | Verify reaping, pins, locks, reservations, and retry isolation |
| Scalar/SIMD hash and frozen-view workloads across relevant targets | Measure dispatch, identity parity, and representation cost |

A test with N identical workers sharing one artifact is distinct from N workers that merely load equal bytes into separate private heaps. Report both logical reuse and physical/private-memory effects.

### 13.5 Admission budgets

Set absolute caps from the target host/product contract and relative thresholds from controlled paired measurements. The thresholds are configuration data with review history—not numbers chosen after a failing run to make it pass.

For a memory repair, require a measured reduction in the affected owner's retained/live bytes, the same semantic result, and no unacceptable elapsed regression. For a performance repair, require lower measured work/time without exceeding the memory contract. Record uncertainty/noise and enough repetitions for any reported percentile; a set of heterogeneous failed compiles is not a benchmark percentile distribution.

For repeated equivalent work after warmup, scratch should return to its documented baseline/capacity envelope. Necessary new module surfaces may grow; charge them explicitly rather than demanding a false constant-memory theorem. Missing attribution remains inconclusive and cannot close a memory-root-cause record.

Sampling can miss short peaks. Record interval and limitations, and use enforcement-level peaks/events where available. Keep the observer outside the workload's failure domain when possible and cap the observer's own storage.

---

## 14. Bug DB grouping and lifecycle integration

### 14.1 Canonical authority and representative groups

Keep `doc/08_tracking/bug/bug_db.sdn` as the canonical tracker and retain existing bug IDs. Extend its established schema through a reviewed migration or an existing compatible relation owner. Do not silently replace it with a new Markdown-only ledger. [R01][r01] [R02][r02]

| Proposed group | Meaning | Primary prevention owner |
|---|---|---|
| MEM-OWN | Missing/incorrect unique, short-borrow, move, or drop enforcement | Language/ownership checker and runtime boundary |
| MEM-LIFE | Temporary/region/resource state outlives its work | Runtime/phase ownership |
| MEM-PIPE | Rich IR overlap, whole-program retention, and readiness barriers | Compiler driver/stage contracts |
| MEM-ALIAS | Hidden copies, COW detachment, and inconsistent mutable aliases | HIR/MIR/interpreter/codegen |
| MEM-CACHE | Duplicate snapshots/materialization, stale identity, unbounded cache generations | Build runner/SCV/cache gateway |
| MEM-WORK | Orphan workers, retained handles, lost task ownership | Process/SOSIX/session supervision |
| MEM-BUDGET | Missing limits, bad admission estimates, registry/resource caps | Resource manager/allocator |
| MEM-VERIFY | Incorrect attribution, stale evidence, missing or bypassed coverage | Metrics/CI/tracking owners |

A report can have one primary group and multiple contributing relationships. Same OOM symptom is not enough to declare duplicate root causes. Label relationships `confirmed-cause`, `contributor`, `symptom-family`, `related-hypothesis`, or `supersedes-evidence` instead of flattening them into one status.

### 14.2 Representative mapping from reviewed reports

The short labels below reference exact report filenames in the sources. Existing statuses are not changed by this table.

| Report | Suggested primary/contributing group | Evidence treatment |
|---|---|---|
| `iso_transfer_sites_missing_move_return_assign_field_2026-08-06` | MEM-OWN | Record reports closed repaired transfer sites; preserve existing fixes and mutation tests [R03][r03] |
| `iso_borrow_check_unreachable_from_interpret_pipeline_2026-08-09` | MEM-OWN / MEM-VERIFY | Record documents HIR interpreter checking gap; reproduce against selected producer [R04][r04] |
| `bootstrap_stage4_ast_hir_overlap_memory_2026-07-27` | MEM-PIPE / MEM-LIFE | Historical overlap and scoped-lifetime work; do not infer full closure from a component repair [R12][r12] |
| `stage3_no_gc_parse_hir_retention_2026-08-25` | MEM-LIFE / MEM-PIPE | Full-program path retention family; preserve same-route acceptance [R13][r13] |
| `stage3_current_source_hir_rss_termination_2026-08-14` | MEM-PIPE / MEM-VERIFY | Multiple contributors and counter limitations; retain attribution boundaries [R23][r23] |
| `readonly_struct_receiver_copy_registry_exhaustion_2026-08-12` | MEM-ALIAS / MEM-BUDGET | Hidden receiver allocation versus registry limit; preserve value semantics [R14][r14] |
| `native_struct_allocation_failure_unchecked_codegen_2026-08-15` | MEM-OWN / MEM-BUDGET | Allocation-failure correctness distinct from source of memory growth [R15][r15] |
| `native_build_worker_oom_global_array_len_stale_in_while_2026-08-18` | MEM-ALIAS / MEM-VERIFY | Final write-back diagnosis and recorded repair override earlier stale-read hypothesis [R11][r11] |
| `bootstrap_snapshot_memory_retention_2026-10-02` | MEM-CACHE / MEM-LIFE | Parent/child authority duplication and per-file scratch [R18][r18] |
| `cold_inventory_validation_scratch_retention_2026-10-06` | MEM-LIFE / MEM-CACHE | Native fixture verified in record; whole cold publication not thereby qualified [R08][r08] |
| `native_build_shard_child_leak_starves_worker_oom_2026-09-18` | MEM-WORK / MEM-BUDGET | Timeout-child cleanup mitigation is distinct from silent child failure cause [R16][r16] |
| `stage3_walk_retains_handle_per_entry_2026-09-25` | MEM-WORK / MEM-LIFE | Bound retained handles and orphan lifetime without weakening source authority [R17][r17] |
| `windows_native_shard_tree_memory_budget_2026-10-03` | MEM-BUDGET / MEM-VERIFY | Preserve cap-transport work and later Windows-unit correction [R10][r10] |
| `native_build_worker_interpreter_heap_grows_unbounded_2026-08-17` | MEM-VERIFY / MEM-CACHE | Read correction before using initial immortal-heap attribution [R09][r09] |
| `simple_test_runner_memory_leak_2026-06-14` | MEM-LIFE / MEM-WORK | Parent-side per-result work needs its own lifetime; child exit is insufficient [R24][r24] |

### 14.3 Proposed relation data—not a current schema claim

The existing database's basic bug rows do not by themselves encode all proof, measurement, and relationship dimensions. Preserve their fields and add reviewed relation tables, using the project's actual SDN parser/writer.

Illustrative table shape only; it has not been executed as a migration:

```sdn
memory_bug_relations |bug_id, group_id, relation, evidence_ref|
    iso_transfer_sites_missing_move_return_assign_field_2026-08-06, MEM-OWN, confirmed-cause, R03
    bootstrap_snapshot_memory_retention_2026-10-02, MEM-CACHE, contributor, R18
```

Maintain normalized related records for requirement IDs, owner paths, source/runtime/producer hashes, affected route/target, reproduction, fix commit, proof roots, acceptance IDs, measured workload, and superseded observations. Prefer stable semantic IDs over source line numbers alone.

Separate fields for `lifecycle`, `cause_confidence`, `implementation_state`, and `verification_scope`. A single Boolean `fixed` cannot express “native fixture passed, full bootstrap pending.” Do not automatically close a bug because its TODO moved or its original file was renamed.

### 14.4 Migration procedure

Read the complete pinned database; reject partial retrieval, parse errors, malformed rows, conflicting IDs, or checksum failures. Take a retained before-image, apply a single-writer transaction, preserve unrelated tables/rows exactly where the format permits, reseal existing integrity headers, and publish atomically.

Run the existing read-only registration and status-consistency tools before proposing changes. Review status synchronization in dry-run mode; do not bulk-apply a heuristic that treats absent or reworded text as proof of completion. The tracking guide documents these limitations. [R20][r20] [R21][r21]

A generated index must not silently omit rows it failed to parse. The bug-generator hardening record is a direct precedent for refusing partial regeneration, not evidence that the original unrelated-file truncation allegation was established. [R22][r22]

### 14.5 Knowledge and recurrence workflow

Update the existing SPipe/LLM wiki, ownership feature-expert guidance, compiler-phase guidance, and bug triage skill with the same requirement IDs and links. Generate short views from canonical data rather than hand-maintaining divergent status summaries.

Before a repair, retrieve the root-cause group, latest correction, closed fix, and acceptance witness. After a failure, correlate phase, allocation site, producer/runtime, process outcome, and snapshot identity. Similarity proposes a relationship; it does not authorize duplicate closure.

When a previously fixed shape recurs, retain the old evidence, add a new dated reproduction, and identify whether the fix was removed, bypassed by another route, absent from the deployed producer, or insufficient for a new case. Those require different repairs.


## 15. Implementation work packages and rollout

### 15.1 Reuse existing owners

These are integration anchors identified in the repository evidence, not permission to introduce parallel implementations.

| Concern | Existing owner or architecture anchor | Planned change |
|---|---|---|
| Typed ownership and moves | `src/compiler/35.semantics/`, `src/compiler/50.mir/`, `src/compiler/55.borrow/` | Common short-borrow/ownership facts, complete cleanup, route parity |
| Interpreter/native integration | `src/compiler/80.driver/` and relevant `src/compiler_rust/` routes | Mandatory shared semantics without redundant full target lowering |
| Runtime ownership | `src/runtime/`, `src/runtime/simple_core/`, `src/compiler_rust/runtime/` | Drop/region/resource/provider parity and fallible allocation correctness |
| Parse reuse | `frontend_parse_cache.spl`, `frontend_shared_parse_cas_v1.spl` | Frozen views, byte-accurate identity, bounded hydration |
| Semantic/artifact cache | `src/compiler/80.driver/cache/`, `driver_hir_cache.spl` | Shared snapshot/read-set authority, leases, single-flight and safe admission |
| Build runner | `src/lib/common/build_manager/`, grouped native manager design | Session immutable owner, per-group reservations, teardown and mappings |
| OS/resource adapters | Existing SOSIX/process/resource owners and watchdog scripts | Accurate platform limits, outcome attribution and propagation |
| Performance facts/lints | Existing compiler-performance memory-efficiency requirements/design | Shared diagnostics and allocation/copy evidence |
| Tracking | Existing `bug_db.sdn`, registration/consistency tools and traceability owners | Root-cause relations and durable acceptance manifest |

Confirm current physical paths and owners before editing. Numbered-layer logical aliases, moved files, and generated mirrors must not cause duplicate owners. Keep target-specific implementations behind shared contracts and preserve 32/64-bit, CPU/SIMD, OS, runtime-provider, and GPU differences explicitly.

### 15.2 Work-package plan

| Package | Implementation work | Dependencies | Exit evidence |
|---|---|---|---|
| WP-00: Evidence baseline | Pin actual producer/runtime/source/DB; classify current reproduction and preserve closed fixes | None | Complete bounded census for the selected repair scope; no inferred fresh status |
| WP-01: Semantic contract | Freeze no-GC unique default, exact short boundaries, call effects, Copy/move compatibility and cleanup order | WP-00 | Positive/negative source corpus and reviewed migration diagnostics |
| WP-02: Common ownership facts | Factor HIR-level facts/checking; CFG joins/loops/partial moves; connect all routes | WP-01 | AC-OWN/AC-BOR on real routes; no interpreter bypass |
| WP-03: Drop and resource completion | Cleanup elaboration, container failure contracts, scope nesting, SFFI/async ownership | WP-01, WP-02 | Native exactly-once and failure-injection corpus |
| WP-04: Proof model and refinement | Lean short-borrow/ownership model; event preservation and axiom audit | WP-01; then WP-02/03 | Admitted proof roots plus implementation-linked fixtures |
| WP-05: Stage contracts | Common Parse/HIR/MIR/OBJ APIs, unit readiness/SCCs, fused scheduling and split replay | WP-02 | Fused/split semantic parity; one-parse counters; no capture-off allocations |
| WP-06: Phase memory | Worker regions, resource cleanup, safe freeze/promotion, bounded queues and trimming | WP-03, WP-05 | Owner-attributed scratch plateau; preserved retained roots |
| WP-07: Immutable session sharing | Reuse gateway/snapshot/journal; leases and frozen mapped views; standalone local session | WP-05, WP-06 | Concurrent read/eviction/crash tests; actual private-memory reduction |
| WP-08: Hash and action identity | XXH3 private policy, BLAKE3 boundaries, collision-safe keys and provider parity | WP-01 identity contract; WP-07 integration | Collision injection, invalidation matrix, scalar/SIMD parity |
| WP-09: Resource supervision | Parent/child budgets, task generations, process-tree cleanup, handle/device limits | WP-07 contracts; can prototype independently | No managed orphans; known nested limits enforced |
| WP-10: Optional diagnostics | Basic/deep/runtime cycles, copy/retention rules using shared facts | WP-02, WP-06 | Positive/negative diagnostic corpus; bounded incomplete outcomes |
| WP-11: Tracking and anti-removal | SDN relations, proof/test manifests, wiring and mutation gates, knowledge updates | WP-00; integrates all packages | Lossless DB test and independent removal/bypass detection |
| WP-12: Product admission | Rebuild correct producers; run target matrix and full real closure under unchanged caps | Integrated prerequisites | Qualified compiler/bootstrap, memory/time receipts, reviewed residuals |

### 15.3 Parallel development lanes

Use a small number of ownership-based lanes, not multiple agents editing the same compiler/runtime choke point concurrently.

**Lane A — Semantics and proof:** WP-01/02/04, owns normative ownership facts and proof contracts. It must not change the short-borrow boundary to accommodate another lane.

**Lane B — Runtime and resources:** WP-03/06 runtime pieces, owns cleanup, regions, resource-bearing storage, and provider parity. It consumes the frozen ownership event contract.

**Lane C — Pipeline and sharing:** WP-05/06 driver pieces/WP-07, owns stage readiness, frozen representations, and cache gateway integration.

**Lane D — Identity and supervision:** WP-08/09, owns trust/identity provider contracts, platform measurements, reservations, task teardown, and crash recovery.

**Lane E — Independent verification and tracking:** WP-10/11/12 verification, owns negative controls, gate-wiring tests, evidence manifests, and read-only review of source/DB scope. Repair authors do not solely determine their own acceptance results.

Freeze shared record layouts and semantic versions before parallel code changes. Publish reviewed contract revisions, require consumers to acknowledge changes, and keep mechanical rename/move commits separate from semantic edits. No lane may resolve conflicts by overwriting newer unrelated bug rows or another lane's accepted tests.

### 15.4 Rollout stages

**Stage A — Reproduce safely.** Establish the current failing route and a bounded minimal fixture. Record baseline owner bytes, elapsed time, actual executable/runtime identity, and process outcome. Do not repeatedly restart an unchanged full-bootstrap command after an unexplained OOM.

**Stage B — Restore semantics first.** Land short-borrow/unique/drop fixes behind a semantic-version and qualification boundary. A new feature flag may select a diagnostic implementation, but an admitted “safe no-GC” label cannot coexist with optional safety checking. Preserve old closed regression controls.

**Stage C — Introduce phase lifetime boundaries.** Validate region/promotion/failure behavior before enabling aggressive reclamation. Integrate fused scheduling and prove split/debug parity using the same transforms. Do not reclaim data early by untyped deep-free calls.

**Stage D — Enable shared artifacts incrementally.** Start with frozen source and existing parse surfaces. Add HIR/MIR/object sharing only when their complete identities and independent representations are admitted. Run shadow comparisons without allowing unverified hits to become success authority.

**Stage E — Qualify concurrency and containment.** Keep isolated groups operational. Enable threads/fibers within qualified groups only after shared/global mutable state is corrected. Prove cap propagation and cancellation before increasing fanout.

**Stage F — Release and watch recurrence.** Rebuild the exact self-hosted producer and run the relevant full closure with the original semantic checks and accepted caps. Then update scoped verification evidence and root-cause relationships. Retain explicit open residuals rather than converting a partial memory improvement into full closure.

### 15.5 Suggested policy configuration

The following is a human-readable **proposed configuration contract**, not executable current SDN syntax or a current CLI guarantee:

```text
no_gc:
    ordinary_owner = unique
    borrow_policy = short_only
    ownership_check = mandatory
    deterministic_cleanup = mandatory
    implicit_shared_rc = forbidden
    tracing_gc = disabled

compile:
    pipeline = fused
    parse_reuse = enabled
    source_parse_count_goal = once_per_exact_parser_input
    phase_capture = none
    global_semantic_checks = preserved
    worker_scratch = unit_owned

build_session:
    immutable_sharing = default
    mutable_worker_state = private
    cache_residency = budgeted
    process_isolation = preserve_required_groups
    standalone_fallback = equivalent_local_session

identity:
    trusted_private = xxh3_128
    nonprivate_or_untrusted = blake3_256
    unknown_trust = strong_boundary_policy
    collision_resolution = required
    algorithms = versioned_and_replaceable

cycle_diagnostics:
    normal = basic_bounded_static
    analysis = deep_bounded_static
    runtime_edges = explicit_debug_only
    automatic_cycle_collection = disabled
    optional_checks_off_disables_ownership_safety = false
```

### 15.6 Comparison with Rust and Java: what to emulate

| Question | Rust | Java | Simple target |
|---|---|---|---|
| Can correctly retained collections exhaust memory? | Yes | Yes | Yes; bounded ownership alone is not a memory budget |
| Are strong shared cycles automatically reclaimed? | `Rc`/`Arc` need non-owning relationships or explicit management | Unreachable managed cycles can be collected | No mandatory collector; handles/regions/weak links and optional diagnostics |
| Does losing ordinary scope ownership mean prompt cleanup? | Normal RAII paths do; deliberate leak/termination exceptions exist | Heap collection is not deterministic resource cleanup | Required deterministic cleanup on supported owner paths |
| Must long-lived graph links become borrows? | Several lifetime/handle/RC representations are available | Managed object references are common | **No; use handles or explicit ownership, keep borrows short** |
| Who prevents whole-program compiler IR retention? | Compiler architecture | Compiler architecture | Fused stages, region lifetimes, shared immutable surfaces |

This comparison concerns mechanisms, not a claim that one language eliminates every memory bug. The relevant primary references are Rust's cycle/forget documentation and Oracle's reachable-object leak guidance. [E01][e01] [E02][e02] [E03][e03]

---

## 16. Final release checklist

A release claiming this recovery must satisfy the following, with exact producer/runtime evidence:

- [ ] No-GC unique ownership is the actual default for ordinary owning references, not only a design statement or an `iso` test fixture.
- [ ] Short borrowing is unchanged in range; returning, storing, capturing, or suspending a borrowed view is rejected as specified.
- [ ] Every admitted execution route enforces the same ownership and cleanup rules.
- [ ] Transfer, partial initialization, container failure, and resource cleanup are correct on real execution paths.
- [ ] The Lean proof roots, assumption audit, and implementation-refinement checks pass within their stated scope.
- [ ] Fused compilation is the default; Parse/HIR/MIR/OBJ remain independently testable and replayable through the same implementations.
- [ ] Necessary global semantics and SCC completion are preserved; diagnostic objects do not count as admitted executables/SMFs.
- [ ] Disabled capture and runtime cycle tracing introduce no capture/edge-recording allocations in ordinary release execution.
- [ ] Phase scratch and resource-bearing regions reclaim correctly without dangling retained references.
- [ ] Immutable sharing reduces actual duplication; worker-local deserialization is measured, not mistaken for zero-copy sharing.
- [ ] Long sessions retire old unpinned generations and keep optional caches within explicit budgets.
- [ ] XXH3 private mode handles forced collisions correctly; untrusted boundaries use their strong identity/authentication policy.
- [ ] Cache keys include exact relevant semantic inputs without unnecessary global invalidation.
- [ ] Task failure cannot leave managed descendants, publication rights, pins, locks, or reservations behind.
- [ ] Metrics use correct units and distinguish payload, reserve, RSS, shared residency, and enforcement charge.
- [ ] The original affected integration/bootstrap route completes within its reviewed limits; reduced fixtures alone do not close it.
- [ ] Existing closed fixes remain protected; new bug relationships and verification scopes are recorded without rewriting history.
- [ ] Required proof/tests cannot be silently removed, skipped, replaced with source-only checks, or bypassed by an alternate route.
- [ ] Memory and performance comparisons use controlled workloads; residual costs and unsupported targets are disclosed.

**Outcome sought:** a compiler and runtime that preserve Simple's short-borrow, no-GC philosophy while preventing repeated ownership loss, unnecessary IR retention, duplicate snapshot materialization, and host-wide exhaustion. The solution is the combination of semantic correctness, bounded lifetimes, immutable reuse, accurate resource admission, and durable evidence—not a longer-borrow language or a mandatory collector.

---

## 17. Sources and evidence register

### 17.1 Repository sources

Repository links below are pinned to the reviewed commit. Some records were examined earlier in the conversation, and the key ownership/cache/inventory records were retrieved again for this document. Their descriptions distinguish historical reports and proposed architecture from executed results. The database retrieval was recovered through the contents API; this document did not run a full database census or migration.

| Ref | Source and purpose |
|---|---|
| [R00][r00] | Reviewed commit identity; limits the repository snapshot used here |
| [R01][r01] | Canonical `bug_db.sdn`; retrieved through the contents endpoint after another action returned no body |
| [R02][r02] | Tracking README: DB-first canonical trackers and generated Markdown views |
| [R03][r03] | Closed iso ownership-transfer record and mutation-tested move-site evidence |
| [R04][r04] | Interpreter route bypassing MIR-based ownership checking; factoring/performance concern |
| [R05][r05] | Proposed origin-neutral resource ownership and short receiver/parameter contracts |
| [R06][r06] | Semantic cache architecture: existing owners, snapshot/gateway/journal/pin target contracts and qualification boundaries |
| [R07][r07] | Grouped native manager: process isolation, complete SCCs, immutable parse cells, and current qualification caveats |
| [R08][r08] | Cold inventory validation scratch retention: narrow native measured regression and remaining acceptance |
| [R09][r09] | Interpreter worker memory report with correction to initial immortal-runtime attribution |
| [R10][r10] | Windows shard memory-cap propagation and later measurement correction |
| [R11][r11] | Runaway global-array loop: final inconsistent write-back diagnosis, repair, and regression |
| [R12][r12] | AST/HIR overlap and streaming/scope history; component repairs versus full admission |
| [R13][r13] | Stage 3 no-GC parse/HIR retention on a full-program route |
| [R14][r14] | Readonly receiver aggregate-copy/registry exhaustion and semantic constraints on elision |
| [R15][r15] | Unchecked native struct allocation failure |
| [R16][r16] | Timed-out shard children remaining resident; cleanup mitigation and unresolved child failure |
| [R17][r17] | Authority-walk handle accumulation and orphan cascade |
| [R18][r18] | Bootstrap parent/child snapshot duplication and file-scratch lifetime |
| [R19][r19] | Existing compiler memory/performance fact, lint, and activation-integrity requirements |
| [R20][r20] | Tracking status synchronization guide and heuristic/registration limitations |
| [R21][r21] | Existing read-only tracking-document registration checker |
| [R22][r22] | Bug-generator partial-parse hardening; original unrelated-file truncation allegation not reproduced |
| [R23][r23] | HIR memory investigation, lowerer reuse, and limits of object-count/byte-counter attribution |
| [R24][r24] | Test-runner parent-side allocation/diagnostic retention report |
| [R25][r25] | Closed-batch review: repeated source bytes do not establish safe semantic cache reuse or benchmark comparability |

### 17.2 External primary sources

| Ref | Source and relevance |
|---|---|
| [E01][e01] | Rust Book: strong reference cycles and weak references |
| [E02][e02] | Rust standard library: `mem::forget`, destructor guarantees, and safe leaks |
| [E03][e03] | Oracle Java troubleshooting: reachable retention and managed/native OOM distinctions |
| [E04][e04] | Rust compiler development guide: arenas and interning |
| [E05][e05] | LLVM/Clang ThinLTO: separate global summary work from parallel backend work |
| [E06][e06] | Official xxHash project: non-cryptographic hashing |
| [E07][e07] | Official BLAKE3 project: cryptographic content hashing and implementations |
| [E08][e08] | Microsoft Job Objects: process grouping, limits, and termination |
| [E09][e09] | Linux kernel cgroup v2 documentation: memory accounting, pressure, and limits |
| [E10][e10] | Lean reference: axioms, `sorryAx`, and auditing transitive assumptions |
| [E11][e11] | Linux `proc_pid_smaps` manual: RSS, PSS, and mapping-level accounting |

[r00]: https://github.com/ormastes/simple/commit/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95
[r01]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/bug_db.sdn
[r02]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/README.md
[r03]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md
[r04]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/iso_borrow_check_unreachable_from_interpret_pipeline_2026-08-09.md
[r05]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/04_architecture/language/resource/resource_declaration_architecture_2026-08-06.md
[r06]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/04_architecture/compiler_semantic_cache_manager.md
[r07]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/04_architecture/compiler/grouped_native_manager.md
[r08]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/cold_inventory_validation_scratch_retention_2026-10-06.md
[r09]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/native_build_worker_interpreter_heap_grows_unbounded_2026-08-17.md
[r10]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/windows_native_shard_tree_memory_budget_2026-10-03.md
[r11]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/native_build_worker_oom_global_array_len_stale_in_while_2026-08-18.md
[r12]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/bootstrap_stage4_ast_hir_overlap_memory_2026-07-27.md
[r13]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/stage3_no_gc_parse_hir_retention_2026-08-25.md
[r14]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/readonly_struct_receiver_copy_registry_exhaustion_2026-08-12.md
[r15]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/native_struct_allocation_failure_unchecked_codegen_2026-08-15.md
[r16]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/native_build_shard_child_leak_starves_worker_oom_2026-09-18.md
[r17]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/stage3_walk_retains_handle_per_entry_2026-09-25.md
[r18]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/bootstrap_snapshot_memory_retention_2026-10-02.md
[r19]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/02_requirements/feature/simple_compiler_performance_memory_efficiency.md
[r20]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/07_guide/infra/tracking/sync_tracking_db_status.md
[r21]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/scripts/check/check-tracking-doc-registration.shs
[r22]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/bug_gen_truncates_unrelated_records_2026-08-21.md
[r23]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/stage3_current_source_hir_rss_termination_2026-08-14.md
[r24]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/08_tracking/bug/simple_test_runner_memory_leak_2026-06-14.md
[r25]: https://github.com/ormastes/simple/blob/c8b4a86ab6876ecb825b4ea42b2c01d388b23a95/doc/09_report/phase3_closed_batch_memory_perf_2026-10-11.md

[e01]: https://doc.rust-lang.org/book/ch15-06-reference-cycles.html
[e02]: https://doc.rust-lang.org/std/mem/fn.forget.html
[e03]: https://docs.oracle.com/en/java/javase/25/troubleshoot/troubleshooting-memory-leaks.html
[e04]: https://rustc-dev-guide.rust-lang.org/memory.html
[e05]: https://clang.llvm.org/docs/ThinLTO.html
[e06]: https://xxhash.com/
[e07]: https://github.com/BLAKE3-team/BLAKE3
[e08]: https://learn.microsoft.com/en-us/windows/win32/procthread/job-objects
[e09]: https://docs.kernel.org/admin-guide/cgroup-v2.html
[e10]: https://lean-lang.org/doc/reference/latest/Axioms
[e11]: https://man7.org/linux/man-pages/man5/proc_pid_smaps.5.html
