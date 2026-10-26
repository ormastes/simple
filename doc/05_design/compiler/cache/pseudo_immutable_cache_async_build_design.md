# Simple: pseudo-immutable cache and asynchronous build architecture

**Design baseline:** 2026-10-26
**Status:** Final consolidated design proposal; not an implementation-completion claim.
**Scope:** Embedded compiler, optional BuildRunner, shared TaskRunner/TestRunner scheduling, source/TLDR cache, binary AST/HIR/MIR, OBJ/BIN/LIB/SMF, compact IDs, concurrent hash algorithms, and resource-aware fiber/process execution.
**Latest requirement incorporated:** HIR contains **optional OS information and optional CPU information**, with explicit target-compatibility semantics.

The data structures, file-layout identifiers, configuration keys, and APIs below are proposed contracts. They are not assertions that these exact names or switches already exist. Repository observations are separated from proposed changes. No native compiler, scheduler, or performance test was executed for this report.

> NOTE (transcription): the original paste was corrupted after requirement R02; sections 1 (rest) through 23 are pending the full text from the author.

## Executive decision

Use **one compilation engine, one cache protocol, and one shared scheduling core**. The embedded compiler works without an external build runner; BuildRunner supplies a managed provider around the same engine; TestRunner submits work through the same scheduling core without becoming a dependency of ordinary compilation.

The default compilation operation is **source → OBJ**, with a fused execution path through the required parsing, semantic, lowering, optimization, and code-generation work. It does not require saving and reloading every intermediate stage. Persisted source MIR is optional. TLDR AST/HIR/MIR and optional executable TLDR OBJ are independently reusable.

Use **pseudo-immutable data**: an immutable artifact payload plus write-once scalar, dense-array, and sparse-hash attribute slots. A missing field is data state, not a future allocation. Asynchronous work is scheduled only for a useful producer, dependency wait, file/cache access, external process, or sufficiently large independent CPU task.

Use **XXH3-128 for fast trusted lookup**, collision-safe local 16/32-bit IDs for references, and algorithm-tagged concurrent digest aliases. Use an admitted cryptographic digest for the normal persistent cache and all untrusted imports; a disposable trusted local-only mode may instead retain exact collision verification. Never use a truncated hash as an identity proof.

Check the requested final artifact first. An unchanged valid OBJ/BIN/LIB/SMF requires **no compilation or linking**. If the destination is missing, materialize the cached result. Only cache misses descend into intermediate compilation stages.

## Contents

1. Requirements and non-negotiable invariants
2. Repository observations and reuse points
3. Architecture and recursive compilation graph
4. Pseudo-immutable fields and attribute storage
5. Identity, XXH3, compact IDs, and concurrent hashes
6. Cache keys, snapshots, and precise invalidation
7. HIR with optional OS and CPU information
8. Binary AST/HIR/MIR format
9. Slot publication, waiting, cancellation, and recovery
10. Compiler/provider interface and default execution
11. Standalone and managed process sequences
12. Early input acquisition and output I/O
13. Shared fiber/process scheduling and resource budgets
14. TestRunner reuse without compiler coupling
15. TLDR precompiled cache sets and optional OBJ
16. OBJ/BIN/LIB/SMF caching and no-change builds
17. Memory lifetime, eviction, and storage compaction
18. Missing pieces identified by the research
19. Implementation plan and ownership
20. Acceptance tests and formal invariants
21. Performance measurement and observability
22. Proposed configuration and rollout
23. Research and repository references

## 1. Requirements and non-negotiable invariants

| ID | Requirement | Binding decision |
|---|---|---|
| R01 | Same compiler API with and without BuildRunner | Swap providers, not compiler implementations. |
| R02 | Default source-to-object compilation | `compile(source, options)` requests OBJ. (remainder of row and R03+ pending — paste corrupted) |
