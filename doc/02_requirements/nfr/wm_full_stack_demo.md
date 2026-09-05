# WM Full-Stack Demo NFRs

Selected by the user on 2026-07-29.

- NFR-001: Native-facing records use scalar fields, explicit status/out
  parameters, generation handles, static dispatch, and no `any`, trait-object,
  raw native pointer, or aggregate out-return ownership boundary.
- NFR-002: The event queue and text arena are bounded. Overflow increments a
  visible counter and never overwrites an unconsumed event silently.
- NFR-003: Window/event/content/pixel registries reject stale generations and
  return to their recorded baseline after the scenario closes all windows.
- NFR-004: The host demo uses one retained presentation resource; no per-frame
  texture/device recreation and no per-pixel allocation/conversion at the
  native boundary.
- NFR-005: After warm-up, retain median and p95 frame time, representative
  event-to-frame latency, and max RSS for the fixed demo fixture. A regression
  over 10% time or 5% RSS within the same host/backend bucket fails.
- NFR-006: Correctness precedes performance: non-black output, semantic state,
  stable color regions, content diversity, and revision ordering must pass
  before timing counts.
- NFR-007: All external/live checks are timeout-bounded and fail closed when the
  display, backend, capture, or native-input evidence is unavailable.
- NFR-008: New non-trivial queue, handle, routing, and lifecycle branches target
  at least 80% branch coverage; capability/status classification targets 100%.
- NFR-009: No new production stub, placeholder pass, hardcoded success, or
  source-scan-only acceptance is permitted.
- NFR-010: Existing unrelated dirty files and active compiler work remain
  untouched and outside this lane's verification scope.
- NFR-011: Each acceptance criterion is run at most once after its last relevant
  change, with no more than three verify/fix cycles.
- NFR-012: SDL, QEMU, HDA, and QRB2210 rows remain explicitly pending or blocked
  until their real runtime evidence exists; host/headless evidence cannot be
  relabeled as those platforms.
