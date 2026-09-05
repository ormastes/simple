# WM/GUI/Web/2D Host Environment Hardening NFRs

Selected NFR option: **B — Retained Per-Device Performance Budgets**.

## Quality Targets

- NFR-001: New or changed host-environment, receipt, and routing code must reach
  at least 98% measured branch coverage; pure classification/validation
  functions target 100%.
- NFR-002: Coverage requires both true and false branch outcomes and cannot be
  increased by mocks standing in for native SIMD, Vulkan, input, or readback.
- NFR-003: Deterministic flat-color/integer fixtures require exact ARGB output,
  zero mismatch, and no blur, tolerance, or memorized-pixel substitution.
- NFR-004: Performance runs use a fixed resolution/workload, warm-up, at least
  20 measured frames or requests, median, p95, throughput, and max RSS.
- NFR-005: Baselines are comparable only within the same OS, architecture,
  physical GPU/device, driver, backend, and rendering mode bucket.
- NFR-006: Within a retained bucket, median or p95 may regress by at most 10%
  and max RSS by at most 5%; output correctness must pass before timing counts.
- NFR-007: Traces reporting data loss, fallback backend identity, synthetic
  handles, incomplete submissions, CPU-mirror readback, or mismatched output
  are invalid measurements.
- NFR-008: A valid RenderDoc `.rdc` is mandatory on prepared Vulkan hosts and
  must be captured outside the timed performance interval.
- NFR-009: All external processes and live UI checks are timeout-bounded and
  retain enough head/tail output plus artifact paths to diagnose failure.
- NFR-010: Current-host mandatory checks execute once per acceptance criterion;
  no green check is rerun unchanged, and verification stops after three
  fix/verify cycles.

## Host Matrix

| Row | Correctness | Performance | Completion |
|---|---|---|---|
| Linux x86 SIMD | Required now | Required now | Must pass |
| Linux Vulkan | Required when live capability is available | Retained bucket | Missing capability is blocked |
| ARM SIMD/NEON | Native host required | Native bucket | Active external-host row |
| RISC-V RVV | Native host required | Native bucket | Active external-host row |
| Chrome/Electron Vulkan | Browser backing + exact ARGB required | Native bucket | Active until proven |
| Simple RenderDoc | Valid `RDOC` capture required | Capture excluded from timing | Active until proven |
