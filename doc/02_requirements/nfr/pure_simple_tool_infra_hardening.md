# Pure-Simple tool and infrastructure hardening NFRs

Selected: NFR option 3 on 2026-07-16.

- NFR-001: Zero shell interpolation of CLI-controlled data at tooling trust
  boundaries.
- NFR-002: Zero placeholder assertions or silent helper stubs in retained
  qualification specs.
- NFR-003: A provenance mismatch must fail before executing the requested
  production command.
- NFR-004: Each focused correctness probe must complete within 30 seconds.
- NFR-005: Warm focused-file `check`, `lint`, and `fmt --check` p95 must be under
  2 seconds on the documented Linux qualification host.
- NFR-006: Warm single-test p95 must be under 3 seconds on the same host.
- NFR-007: The test-runner parent must remain below 1 GiB max RSS for the
  representative 1,000-test batch, with batch-boundary reclamation evidence.
- NFR-008: Cache hit and miss runs must produce equivalent outcomes; invalidated
  inputs must not reuse stale results.
- NFR-009: MCP and LSP warm startup must be under 1 second, representative warm
  request p95 under 200 ms, and max RSS under 1 GiB on realistic fixtures.
- NFR-010: Linux and Windows production launchers must enforce equivalent
  provenance, native-artifact preference, argument forwarding, and fail-closed
  behavior.
- NFR-011: Deployment must be atomic and leave no interval where a failed or
  unverified candidate is the only production runtime.
- NFR-012: After the bootstrap boundary, production routes must use no Rust
  seed/debug fallback; any temporary bootstrap dependency must be explicit,
  named, and excluded from production qualification evidence.
