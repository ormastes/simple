<!-- codex-design -->
# Slang KV cache optimization system-test plan

Date: 2026-09-09

| Requirement | Evidence |
|---|---|
| REQ-001, NFR-002–004 | Reproducible real-provider benchmark receipt with immutable identities and five paired samples |
| REQ-002 | Cold, exact-repeat, alternating, eviction, and A -> A+suffix workload rows |
| REQ-003, REQ-006 | Mode-tagged counters and byte fields; no snapshot-counter substitution |
| REQ-004, REQ-005 | Unit owner fixtures for full-page reuse, partial-tail COW, suffix-only prefill, abort, and stale/wrong namespace |
| NFR-001 | Existing full-vector real-provider parity plus generated-token equality |
| NFR-005 | Zero live request/reservation references and bounded high-water assertions after every workload |
| NFR-006–007 | Baseline-only report and public synthetic prompts |

The system scenario invokes one bounded launcher and asserts its terminal PASS
marker. Detailed matrices remain folded implementation evidence. No fixed
speedup threshold is admitted in this wave.
