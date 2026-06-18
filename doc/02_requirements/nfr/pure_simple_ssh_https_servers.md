# NFR Requirements: Pure Simple SSH and HTTPS Servers

## Selected Option

NFR Option 1: Conservative Release Gate.

## Requirements

- NFR-001: Release-mode SSH and HTTPS server paths must have focused unit or integration coverage for the selected protocol boundary behavior.
- NFR-002: At least one hosted Linux smoke must cover each release-mode server path before the lane is marked complete.
- NFR-003: SimpleOS live gates must be documented as required release evidence; if QEMU or platform state blocks them, the blocker must be concrete and linked from the lane docs.
- NFR-004: Verification must include malformed or failed input coverage for the selected initial security surface: failed SSH auth or malformed SSH packet, and failed TLS handshake or malformed TLS record.
- NFR-005: Verification must include `sh scripts/setup/install-spipe-dev-command.shs --check`.
- NFR-006: Verification must include `find doc/06_spec -name '*_spec.spl' | wc -l` returning `0`.
- NFR-007: New or changed executable SSpec scenarios must be mirrored by generated/manual Markdown under `doc/06_spec`.

## Non-Goals

- Strict cross-platform live-gate pass for every SSH and HTTPS path is not required for this first selected slice if a concrete external blocker is recorded.
- Startup/RSS/latency benchmarks are not required unless the implementation introduces a new hot-path cache, repeated scan, or performance-sensitive wrapper.
