<!-- codex-research -->

# SimpleOS Enhancement Non-Functional Requirements

- NFR-001: Authority is monotonic: child authority is a subset of delegable
  parent authority and no runtime path grants authority from a role string,
  namespace flag, syscall filter, or empty capability set.
- NFR-002: Handles are generation-checked; recursive revocation invalidates
  descendants and a restarted workload has no stale grants.
- NFR-003: Isolation and resource controls fail closed and are hierarchical.
- NFR-004: PID1 service start, dependency readiness, failure/restart,
  quarantine, and shutdown have retained QEMU evidence.
- NFR-005: Security decisions, delegation lineage, image identity, broker use,
  approval, exit, and restart are auditable without exposing raw secrets.
- NFR-006: Workload policy is compiled once at spawn and hot security paths do
  no full-tree scan, repeated file read, or subprocess launch.
- NFR-007: The design is regression-protected by focused unit/SSpec scenarios,
  adversarial tests, and later formal invariants/fuzzing; unavailable host rows
  remain tracked as blocked rather than reported as PASS.
