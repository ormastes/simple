# Slang serial exact-prefix cache requirements

Date: 2026-09-08. Status: selected implementation slice from the user-approved
SPipe + Slang research contract.

- REQ-001: Preserve request isolation on every mismatch or restore failure.
- REQ-002: Reuse state only when the cached token sequence is an exact prefix.
- REQ-003: Recompute the prefix boundary token before suffix evaluation.
- REQ-004: Keep weights resident and cache ownership inside the backend context.
- REQ-005: Expose honest capability and cumulative hit/miss/token counters.
- REQ-006: Free snapshot storage and reset counters during backend teardown.
- REQ-007: S1 remains the single-entry compatibility floor. A later explicitly
  versioned precursor may retain several immutable serialized snapshots while
  execution remains serial; it must not claim paged or concurrent ownership.
