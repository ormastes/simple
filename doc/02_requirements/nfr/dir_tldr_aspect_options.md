# dir_tldr_aspect: NFR Options

**Status: SELECTED 2026-11-02; N3a/N3b deleted. Final: `dir_tldr_aspect.md`.**

| ID | Option | Pros | Cons | Effort | Verify |
|---|---|---|---|---|---|
| N1 | Dir TLDR check (hit) ≤5 ms p95 per dir; build (miss) ≤200 ms per 100 files | Keeps the check off the critical path | Must be measured on the real tree | S | bench spec on `src/compiler` |
| N2 | First `.o` ≤10 s preserved under the per-dir policy (hard gate) | Honours the standing rule | May force splitting | S | timed build log |
| N4 | Clean build wall with the per-dir policy ≤ per-file baseline +3%; warm no-op ≥30% faster | Proves the value | Needs a baseline | M | A/B runs |
| N5 | Determinism: two clean builds produce identical woven object digests | Reproducibility | | S | digest diff spec |
| N6 | Plugin reuse: N dirs with an identical normalised plugin → 1 instance (counter) | Directly tests the request | | S | counter assert |
| N7 | Aspect change re-weaves only the affected dir union (measured count = expected count) | Incremental precision | Needs a fixture tree | M | counter spec |
| N8 | Stale or corrupt dir TLDR is never admitted (0 false admits across fault injection) | Safety | Fault harness | M | fault-injection spec |
