# GPU Dynamic Backend and Full Offload NFRs

Selection: **Tier 3 — aggressive throughput**.

- NFR-GPU-DYN-001: Exact CPU-oracle parity is mandatory; mismatch tolerance is
  zero for the selected integer/pixel fixtures.
- NFR-GPU-DYN-002: Provider load and submission waits are bounded to five
  seconds and fail closed with a typed reason.
- NFR-GPU-DYN-003: Warm provider negotiation p95 shall be below 5 ms.
- NFR-GPU-DYN-004: Cached IR-to-submit host overhead p95 shall be below 50 us
  for each representative promoted batch.
- NFR-GPU-DYN-005: GPU promotion requires at least 1.50x CPU throughput or GPU
  end-to-end latency no greater than 0.67x the CPU latency.
- NFR-GPU-DYN-006: Warm p95 performance regression shall not exceed 2% against
  the retained comparable baseline.
- NFR-GPU-DYN-007: Evidence shall include sustained queue-saturation and a
  30-minute soak with bounded handles, sessions, completions, device memory,
  host pinned memory, and max RSS.
- NFR-GPU-DYN-008: Profiles shall report transfer bandwidth, device-memory and
  pinned-memory use, power when the native tool exposes it, warmup/sample
  counts, median, p95, and workload/artifact identity.
- NFR-GPU-DYN-009: No promoted rendering frame may reload the provider or
  rebuild an unchanged IR artifact on the hot path.
- NFR-GPU-DYN-010: Missing native tooling or hardware is BLOCKED, never PASS;
  source inspection, emulator output, or cached evidence cannot substitute for
  a fresh native row.
