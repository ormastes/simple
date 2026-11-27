# dir_tldr_aspect: NFR Requirements (FINAL)

**Status: SELECTED by the user (2026-11-02).** Selection: N1, N2, N4, N5, N6, N7, N8 (N3a/N3b not selected and deleted).
Implementation deferred; verification is the fail-fast spec `test/03_system/app/compiler/feature/dir_tldr_aspect_nfr_spec.spl` (TODO 430).
Feature requirements: `doc/02_requirements/feature/dir_tldr_aspect.md`.

| NFR | Requirement | Verify |
|---|---|---|
| NFR-DTA-N1 | Dir TLDR check (hit) at most 5 ms p95 per dir; build (miss) at most 200 ms per 100 files | bench spec on `src/compiler` |
| NFR-DTA-N2 | First `.o` at most 10 s preserved under the per-dir policy (hard gate) | timed build log |
| NFR-DTA-N4 | Clean build wall with the per-dir policy at most per-file baseline +3%; warm no-op at least 30% faster | A/B runs |
| NFR-DTA-N5 | Determinism: two clean builds produce identical woven object digests | digest diff spec |
| NFR-DTA-N6 | Plugin reuse: N dirs with an identical normalised plugin create 1 instance | counter assert |
| NFR-DTA-N7 | Aspect change re-weaves only the affected dir union (measured count = expected count) | counter spec |
| NFR-DTA-N8 | Stale or corrupt dir TLDR is never admitted (0 false admits across fault injection) | fault-injection spec |
