# Release Beta NFR Requirements

Selected option: **B — Bounded bootstrap resources**.

- NFR-001: Every candidate and verification bootstrap sets `SIMPLE_NO_STUB_FALLBACK=1`.
- NFR-002: Transitive facade-glob traversal terminates cycles with bounded repeated work while preserving the reachable names allowed by the existing depth cap.
- NFR-003: Retain per-stage elapsed-time and maximum-RSS evidence; a build showing unbounded growth or repeated identical expansion is rejected.
- NFR-004: The accepted facade-glob implementation must not regress compile time materially relative to the retained baseline; the current memoized probe target is 191.1 seconds versus 253.9 seconds baseline for 728 modules.
- NFR-004a: Release admission caps isolated Stage 3 elapsed time at 254 seconds and each strict stage at 24 GiB maximum RSS. Overrides are diagnostic only and must be recorded with their justification; they do not silently redefine release acceptance.
- NFR-005: Release checks are fail-closed, bounded, and retain actionable logs naming the missing/invalid artifact or platform row.
- NFR-006: Reuse stable caches only where provenance proves the inputs; a cache hit is not release evidence and stale outputs are rejected.
- NFR-007: Required package checksums and executable provenance bind artifacts to the selected version and source revision.
