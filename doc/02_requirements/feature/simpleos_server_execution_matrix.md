# Requirements: SimpleOS server execution matrix

The user selected these requirements directly on 2026-08-14.

- REQ-001: ARM64 QEMU shall boot current SimpleOS and filesystem-resolve a real
  web/database server executable.
- REQ-002: The ARM guest shall answer host-visible HTTP health and file probes.
- REQ-003: The ARM guest shall persist a DB value across a fresh boot using the
  same filesystem image.
- REQ-004: A retained receipt shall bind physical UNO Q identity, OS context,
  source revision, filesystem path, and executable hash.
- REQ-005: UNO Q shall filesystem-launch the server and pass HTTP file plus DB
  write/read/restart probes.
- REQ-006: UNO Q shall pass a forced CPU-only run with GPU unselected.
- REQ-007: UNO Q shall pass a distinct Adreno/Vulkan submit, completion, and
  readback run while server probes remain live.
- REQ-008: Linux shall compare equivalent Simple HTTP/DB operations with nginx,
  PostgreSQL, and SQLite under retained controls.
- REQ-009: CUDA rows shall accelerate only an identified compute stage and
  shall not be presented as socket or durable-storage acceleration.
- REQ-010: CUDA shall remain an optional dynload feature absent from CPU-only
  execution.
- REQ-011: A measured Simple deficit shall trigger no more than three
  semantics-preserving Pure-Simple optimization cycles, or a concrete blocker.
- REQ-012: Marker apps, host substitution, Linux-as-SimpleOS claims, and
  receiptless results shall receive no acceptance credit.
