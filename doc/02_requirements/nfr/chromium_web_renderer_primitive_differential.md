<!-- codex-research -->
# Chromium primitive oracle library NFRs

Selected: NFR Target 2 — staged semantic oracle.

- NFR-CHROME-001: Validate all ABI-v1 symbols, library/broker hashes, bounds,
  and exact-once lifetime before accepting a session.
- NFR-CHROME-002: Require real DOM/style/layout/paint/input evidence now; keep
  GPU and cross-renderer performance comparisons unavailable until genuine
  device-origin evidence satisfies the strict promotion contract.
- NFR-CHROME-003: Plugin initialization p95 is at most 3 seconds; canonical
  normalization p95 is at most 5 ms for at most 512 events and 1 MiB output.
- NFR-CHROME-004: Peak bridge RSS is at most 1 GiB and sessions/processes are
  released deterministically on success, error, timeout, and caller shutdown.
- NFR-CHROME-005: Tests cover symbol/version/hash rejection, response bounds,
  malformed JSON, broker crash/timeout, repeated calls, and exact-once release.
