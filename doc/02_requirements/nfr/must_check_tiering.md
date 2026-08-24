# Must-Check Tiering NFRs

- NFR-MCT-001: The focused push self-test, committed-ref fixture, and a
  representative production-tree push path must each complete within 10
  seconds on the development host. One hook invocation accepts at most two
  unique ref updates and deduplicates identical updates.
- NFR-MCT-002: Push behavior is read-only with respect to repository state and
  uses a closed gate allowlist; registry text cannot inject arbitrary commands.
- NFR-MCT-003: Ledger replacement is deterministic for the same fingerprint,
  timestamp, commands, verdicts, and evidence.
- NFR-MCT-004: PASS evidence must be non-symlinked, SHA-256 bound, source-fresh,
  and individually timestamped. TODO/blocked rows use `passed_at_utc=never`.
- NFR-MCT-005: No full bootstrap is required merely to execute the push hook.
  The initial all-TODO baseline is reported quickly while structural gates stay
  mandatory; after first promotion, missing, stale, or downgraded required
  bootstrap evidence fails closed.
- NFR-MCT-006: Production PASS evidence is repository-contained, non-symlinked,
  committed, SHA-256 bound, read from the exact pushed revision, and limited to
  64 MiB aggregate input per ledger validation.
- NFR-MCT-007: A production bootstrap recorder refuses to label evidence with
  `HEAD` while any fingerprinted input differs from that revision.
- NFR-MCT-008: Size evidence uses equivalent stripped native Simple and Go
  artifacts with hashes. Startup evidence compares cold and warm Simple
  interpreter launch with equivalent Python, Bun, and Go programs. Throughput
  evidence compares semantically equivalent native Simple, Rust, and Go work;
  a Rust-seed interpreter measurement cannot promote a native-Simple row.
