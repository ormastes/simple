# NFR: MC/DC, RT, and HAL Hardening

Date: 2026-08-25
Selected profile: N2 — Mission-critical balanced

- NFR-001: Static-off hot paths contain zero MC/DC probes, allocations, dispatch,
  or attributable text-size delta.
- NFR-002: A static-on probe is O(1), performs zero heap allocations/source-name
  copies/global-lock operations, and produces no more than 5% representative
  workload slowdown or 5% peak-RSS increase.
- NFR-003: Dynamic dormant overhead is at most 1% with zero allocation; enabled
  overhead is at most 10% on the same fixture.
- NFR-004: Recording uses fixed owner-local buffers, default 1 MiB per owner plus
  a configurable global cap, with explicit drop/overwrite counters.
- NFR-005: MC/DC analysis has expected O(E*C) time and bounded auxiliary memory;
  no O(E-squared) independence-pair scan is permitted.
- NFR-006: HAL comparison has bounded workers, queues, timeouts, diagnostics, and
  output; results commit in deterministic order and destructive effects occur once.
- NFR-007: Every touched hot path is reviewed in this order: complexity,
  allocations/copies, layout/locality, loop hoisting, dispatch, synchronization,
  and logging.
- NFR-008: Compare the same realistic baseline before/after and report timing,
  peak RSS, allocation evidence, saturation behavior, and correctness together.
- NFR-009: Run the Simple optimizer on touched `.spl` code where applicable.
- NFR-010: Preserve Pure Simple ownership; C/Rust changes are limited to already
  delegated runtime/FFI boundaries and cannot substitute for Pure Simple.
