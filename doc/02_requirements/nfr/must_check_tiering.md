# Must-Check Tiering NFRs

- NFR-MCT-001: The focused push self-test and a committed-ref fixture path must
  each complete within 10 seconds on the development host.
- NFR-MCT-002: Push behavior is read-only with respect to repository state and
  uses a closed gate allowlist; registry text cannot inject arbitrary commands.
- NFR-MCT-003: Ledger replacement is deterministic for the same fingerprint,
  timestamp, commands, verdicts, and evidence.
- NFR-MCT-004: PASS evidence must be non-symlinked, SHA-256 bound, source-fresh,
  and individually timestamped. TODO/blocked rows use `passed_at_utc=never`.
- NFR-MCT-005: No full bootstrap is required merely to execute the push hook;
  missing required bootstrap evidence is reported quickly and fails closed.
