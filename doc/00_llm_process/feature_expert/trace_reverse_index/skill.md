# Feature expert: trace reverse index and generation cache

Plan: traceability plan 2026-11-14, sections 2.2 and 3.4. Requirements: REQ-TRC-017, TRACE-009, CTX-006.

## Files
- `src/lib/common/traceability/reverse_index_v1.spl`: `trace_reverse_index_build_v1(TraceGraph)` builds `(relation, target) -> sorted unique sources` in one pass over edges; `trace_reverse_lookup_v1(index, relation, TraceEntityIdV1)` is a dict lookup, no edge scan. Dangling targets are indexed.
- `src/lib/common/traceability/reverse_index_cache_v1.spl`: `TraceGenerationKeyV1` (path, presence, length, SHA-256) and `trace_cache_decide_v1`; only an identical key is a Hit, mtime is never used, an unusable digest is `DigestUnavailable`. `trace_reverse_index_cached_v1` reuses the entry on Hit, else rebuilds.
- Spec: `test/01_unit/lib/common/traceability/reverse_index_spec.spl` (parity with a brute-force scan per node and relation; cache decisions).

## Rules
- Pure: the caller reads the snapshot, computes its key and decodes the graph.
- A `DigestUnavailable` result is rebuilt but its key can never hit later, so the caller should not treat it as trusted.
- Pattern copied from `src/app/mcp/ctx_index_cache.spl`.

## Not done
- Not wired into `trace missing` or the snapshot loader (they take the model `TraceGraph` without a snapshot file key today; wiring needs the loader to compute the digest).
- Index covers edge relations only; `path -> declarations`, `run -> cases`, negative dependencies (plan 2.2) are separate indexes.
