<!-- codex-design -->
# Slang KV cache optimization NFR requirements

Date: 2026-09-09
Selection: NFR option 1.

- **NFR-001:** Require exact generated-token parity and the existing bounded
  numerical parity contract.
- **NFR-002:** Run five paired repetitions with alternating mode order and
  publish raw samples, median, and range with immutable input identities.
- **NFR-003:** Use monotonic timing. Report TTFT as unavailable when generation
  reaches EOG before emitting a token.
- **NFR-004:** Keep logical page bytes, provider-reported physical bytes,
  snapshot bytes, and process maximum RSS distinctly labelled.
- **NFR-005:** All workload runs must finish with no live requests,
  reservations, or leaked page ownership and must stay inside configured page
  and byte bounds.
- **NFR-006:** The first optimization PR is baseline-only for latency: publish
  regressions honestly and do not invent a speedup threshold or enable physical
  mode by default.
- **NFR-007:** Use public synthetic prompts and make no cross-tenant cache or
  privacy claim.
