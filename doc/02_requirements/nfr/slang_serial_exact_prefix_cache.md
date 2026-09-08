# Slang serial exact-prefix cache NFR

Date: 2026-09-08. Status: selected.

- NFR-001: Cached and uncached prompt evaluation must preserve token-context
  semantics; a mismatch must never observe stale request state.
- NFR-002: A hit evaluates only one boundary token plus the uncached suffix.
- NFR-003: Prefix matching is linear in cached-prefix tokens with no hashing or
  approximation in the baseline.
- NFR-004: Snapshot allocation is bounded to one backend-owned sequence state.
- NFR-005: Missing production runtime/model evidence is reported as unavailable,
  never converted into a latency or memory claim.
