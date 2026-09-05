<!-- codex-research -->
# Parser Framework — Feature Requirements

**Selection:** F2 — Complete phased framework
**Selected:** 2026-07-31

## Goal

Provide one generic parser runtime and canonical Simple dialect whose scalar, SIMD, GPU, incremental, and measured-auto modes emit the same deterministic parse result over a memory-bounded span/index representation.

## Requirements

- **REQ-001 — Canonical representation.** One immutable UTF-8 snapshot owns source bytes. Tokens contain half-open byte spans plus interned value IDs where needed; syntax uses typed index-based SoA arenas with stage-bounded lifetimes. The canonical path must not create per-character source objects or copy token lexemes.
- **REQ-002 — Stable contracts and Simple adapter.** `ParseDialect`, `ParseRuntime`, `ParseRequest`, `ParseResult`, `ParseActionSink`, parser policies, tag/mapping types, and `StageReceipt` are public common-layer contracts. The Simple adapter routes the current canonical grammar through those contracts without changing byte, token, syntax, or diagnostic behavior.
- **REQ-003 — Deterministic scalar result.** Repeated scalar parses commit tokens, nodes, tags, mappings, indexes, diagnostics, and invalidation in stable source order and produce identical deterministic receipt fields plus semantic `deterministic_hash`, independent of allocation IDs or worker completion order. Executor provenance and timing telemetry are observable but excluded from semantic equality.
- **REQ-004 — SIMD structural indexes.** The SIMD executor validates UTF-8 and classifies delimiters, quote/escape state, newlines, and indentation across block boundaries. The scalar grammar consumes the ordered index and produces the exact scalar-oracle result.
- **REQ-005 — Bounded GPU lexical/region execution.** GPU lexing uses finite chunk transition summaries, associative source-order composition, overflow-checked integer count/scan/emit, and disjoint ordered output ranges. Eligible Simple top-level declarations and function bodies may parse as regions; unsupported state counts, nesting, placement, or input sizes report explicit scalar fallback. Atomic append and the current object-heavy token/AST representation are forbidden.
- **REQ-006 — Incremental equivalence.** Edits expand to lexical stabilization boundaries and changed parse regions. Unchanged arena regions are reused only when lexical/grammar context is compatible; the result emits retained old-to-new mappings and invalidation and equals a clean full reparse of the edited snapshot.
- **REQ-007 — Demand and measured dispatch.** Disabling `TagDemand` performs zero tag/index allocation. Retained per-stage benchmarks measure scalar, SIMD, and GPU end-to-end costs and drive `auto` crossover thresholds; no optimized mode promotes without exact result comparison.
- **REQ-008 — Evidence and traceability.** Modern SSpec scenarios, unit/integration tests, generated operator manual, benchmark evidence, architecture/detail design, agent-task ownership, and guide material trace every requirement. Unsupported rows remain explicit and final high-capability review verifies the merged lane.

## Scope

The framework and Simple dialect are included. Clang C/C++ parsing, HTML tree-building semantics, other consumer dialect implementations, and resident-GPU arena placement remain outside this lane. Hybrid SIMD execution has no GPU-placement dependency.

## Acceptance mapping

| Requirement | Acceptance criteria |
|---|---|
| REQ-001 | AC-1 |
| REQ-002 | AC-2 |
| REQ-003 | AC-3 |
| REQ-004 | AC-4 |
| REQ-005 | AC-5 |
| REQ-006 | AC-6 |
| REQ-007 | AC-7, AC-8 |
| REQ-008 | AC-9, AC-10, AC-11, AC-12 |
