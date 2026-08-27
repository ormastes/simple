# SFFI v2 admission acceptance NFRs

**Status:** Selected by user on 2026-08-27 — `developing`

- **NFR-SFFI-ACC-001:** Admission occurs only at load/activation time; admitted
  typed calls do no per-call hashing, signature verification, symbol lookup,
  registry map lookup, lock, retry, or generic marshalling.
- **NFR-SFFI-ACC-002:** Fixture execution is bounded, deterministic, and
  uses canonical LF manifests plus exact byte hashing for binary artifacts.
- **NFR-SFFI-ACC-003:** Tests distinguish PASS, FAIL, BLOCKED, and DEVELOPING;
  a missing provider/fixture never passes or skips a release gate.
- **NFR-SFFI-ACC-004:** Error results contain no secret key bytes, raw pointer
  values, or full untrusted artifact payloads.
