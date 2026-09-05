<!-- codex-research -->
# Parser Framework — Non-Functional Requirements

**Selection:** N2 — Balanced promotion targets
**Selected:** 2026-07-31

- **NFR-001 — Exact parity.** Every implemented execution mode produces identical ordered tokens, syntax, tags, mappings, indexes, diagnostics, invalidation, deterministic receipt fields, and semantic deterministic hash on the acceptance corpus. Backend, mode, fallback provenance, and elapsed telemetry may differ and are excluded from equality/hash.
- **NFR-002 — Memory.** Canonical multifile peak parser RSS is at most 50% of the retained pre-change baseline, and completed-stage arena release does not produce monotonic retained growth. `TagDemand` disabled reports zero tag/index allocations.
- **NFR-003 — Scalar compatibility.** Median scalar framework time is no more than 10% slower than the existing scalar oracle on the retained representative corpus.
- **NFR-004 — Optimized promotion.** SIMD or GPU becomes eligible for `auto` only when retained median end-to-end time is at least 1.5× faster than scalar for that stage and size class. GPU time includes transfer, launch, synchronization, and ordered result materialization; device-only throughput is reported separately.
- **NFR-005 — Incremental latency.** For edits touching at most 1% of source bytes, median incremental latency is at most 25% of clean full-reparse latency while satisfying NFR-001.
- **NFR-006 — Safety and determinism.** All counts and offsets overflow-check before allocation; optimized modes fail closed or record explicit fallback; results never depend on hash iteration, arena/interner IDs, atomics, or worker completion order.
- **NFR-007 — Evidence quality.** Measurements retain host/backend identity, exact binary/source revision, fixture identity, warm/cold classification, median, p95, maximum RSS, allocation counters, crossover decision, and result-parity status. Each acceptance command is run at most once unchanged per session.
