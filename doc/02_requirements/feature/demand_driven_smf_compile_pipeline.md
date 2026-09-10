# Requirements — Demand-Driven SMF Compile Pipeline

The following requirements are selected.

- **REQ-001:** SMF is the canonical reusable package/class archive and stores independently addressable export, import, type, generic, HIR-summary, MIR, object, debug, dependency, and receipt sections.
- **REQ-002:** `simple build`, `check`, `run`, and `test` resolve the nearest `simple.sdn` package by default; explicit file and `--source` usage remain compatible.
- **REQ-003:** Warm operations perform no recursive source-root scan and read only the package index plus required SMF sections.
- **REQ-004:** Imports first read a bounded source head or SMF header/index. Comments, whitespace, and import declarations may be discovered without parsing bodies.
- **REQ-005:** Import metadata proxies materialize declarations, generic bodies, HIR bodies, or native symbols only when a semantic operation requests them.
- **REQ-006:** No unresolved proxy or virtual type may enter MIR; materialization failure is deterministic and fail-closed.
- **REQ-007:** HIR supports deferred bodies and records requested operations; it concretizes the minimum closed set before MIR lowering.
- **REQ-008:** A reusable scheduler library serves compiler, test runner daemon, MCP/LSP, and background optimizer queues.
- **REQ-009:** The persisted action graph supports dynamic import edges, SCC ordering, work pools, single-flight execution, cancellation, memory budgets, restat/semantic early cutoff, and buffered diagnostics.
- **REQ-010:** Reusable outputs use a host-shared, project-namespaced, content-addressed cache; daemon memory is never canonical authority.
- **REQ-011:** Development uses baseline bytecode or low-latency Cranelift artifacts; LLVM optimization and native promotion run asynchronously unless explicitly requested.
- **REQ-012:** Runtime and standard-library SMFs are precompiled and rebuilt only when their action/ABI identities change.
- **REQ-013:** Generic implementations share ABI/layout shapes with dictionaries; full specialization is explicit or profile-guided.
- **REQ-014:** File and stdio operations are asynchronous internally while preserving synchronous-looking Simple source semantics.
- **REQ-015:** CPU SIMD lexical acceleration is admitted by benchmark; GPU parsing is notification/experimental only until a measured crossover proves benefit.
- **REQ-016:** Background work never delays a warm cache hit and cannot alter the result of the active immutable snapshot build.
- **REQ-017:** Existing single-file commands remain valid; ambiguous unbounded entry discovery emits migration guidance rather than silently scanning.
- **REQ-018:** Common Simple file I/O is asynchronous-first and exposes one portable read-only file-view API. Its default `auto_map` policy attempts `mmap`/platform mapping whenever safe and suitable, then falls back to asynchronous buffered reads with identical bounds, snapshot, error, and no-follow semantics.
- **REQ-019:** Lack of mapped-file support may reduce performance but must never disable SMF/package loading, lazy section access, parsing, or compilation.
- **REQ-020:** Callers may select `must_map` (mapping failure is returned), `prefer_map` (attempt mapping, then buffered fallback), or `buffered` (never map). `auto_map` is the common default and may choose bounded mapped windows from file size, access pattern, platform capability, and address-space budget.

## Performance acceptance

- **NFR-001:** Warm no-change package decision: p50 <= 100 ms, zero source opens.
- **NFR-002:** Warm no-change command: p50 <= 500 ms.
- **NFR-003:** Ordinary package edit: p50 <= 3 s.
- **NFR-004:** Broad dependent edit: p50 <= 15 s.
- **NFR-005:** Clean matched build: <= 2x comparable Go after stabilization.
- **NFR-006:** Daemon loss changes latency only, never correctness.
