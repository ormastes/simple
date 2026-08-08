# GPU Renderer Processing Backend NFRs

- NFR-001: Backend artifacts are deterministic for identical ProcessingIR,
  generator version, target, ABI, and semantic identity.
- NFR-002: Validation and unsupported-input rejection occur before device, cache,
  counter, upload, or fallback mutation.
- NFR-003: Native evidence records compiler/validator identity, physical device
  identity, positive backend handle, exact readback source, and mismatch count.
- NFR-004: Cached artifacts invalidate on every operation, shape, binding, target,
  ABI, source, entry-point, and generator-version semantic change.
- NFR-005: Host-independent generation performs no device probing or full-tree
  scan and exposes a measurable generation-time/RSS test contract.
- NFR-006: Unavailable bootstrap, macOS, or Windows rows retain exact bounded
  resume commands and are never converted to skips, synthetic success, or CPU
  evidence.
- NFR-007: Environment and communication probes are bounded, retain machine-
  readable receipts, perform no repeated full-tree scan, and distinguish
  `physical-device`, `emulator`, `software`, and `blocked` evidence classes.
- NFR-008: Each owned ProcessingIR backend, translation, and emulator module
  reaches at least 80% measured branch-outcome coverage. Reports retain the
  exact source scope, branch numerator and denominator, and tooling limitation;
  scenario counts or line coverage cannot substitute for branch coverage.
