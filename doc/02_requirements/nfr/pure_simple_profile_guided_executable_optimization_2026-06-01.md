# Pure Simple Profile-Guided Executable Optimization NFRs

Date: 2026-06-01

Selection: measured profile-guided optimization plus bare-metal trap-budget
gates.

## Non-Functional Requirements

- NFR-001: Profile loading must be opt-in; disabled profile loading must not
  perform profile file I/O in hot paths.
- NFR-002: Profile-load startup overhead must stay under 5% on representative
  fixtures that already import the profile loader.
- NFR-003: Native profile-counter runtime overhead must stay under 3% on the
  native smoke fixture when instrumentation is enabled.
- NFR-004: Pure-Simple layout planning must report before/after size, startup
  or runtime evidence, changed placement, and skipped or rejected candidates.
- NFR-005: Layout transforms must preserve entry, symbol, relocation, and
  manifest mapping invariants; unsafe transforms must be rejected.
- NFR-006: Breakpoint counters must auto-disarm when trap overhead exceeds
  budget, and hot loop sites must downgrade to sampled-only behavior after
  calibration.
- NFR-007: Breakpoint patch cleanup must be idempotent across normal stop,
  panic, watchdog timeout, failed single-step, and target reset paths.
- NFR-008: QEMU or hardware-unavailable evidence must be separated from any
  bare-metal speedup claim.
- NFR-009: Verification must include focused SPipe specs, current runtime
  checks, `git diff --check`, and the `doc/06_spec` executable-spec layout
  guard.
