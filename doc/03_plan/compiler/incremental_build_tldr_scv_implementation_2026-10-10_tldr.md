# Incremental compiler implementation plan — TLDR

All 28 selected requirements and WP0–WP11 remain in scope. Implementation,
native qualification and the full bootstrap/test objective are incomplete.

- Keep canonical `.tld` headers and exact content/generation/provider admission.
- Preserve full bootstrap authority on a complete captured source projection.
- Reuse the existing SCV durable owner, compiler gateway and task scheduler.
- The index has nine distinct observed structural passes; the topology timeout
  remains unknown and eleven batch cases are unrun. No native/perf claim.
- Fifteen SourceEdit semantic cases passed once. Preserve the original
  controller attribution failure and its retained-only reconciliation.
- Fix the reviewed cold codec parameter-loss blocker before enabling reuse.
  Connected IDE/SCV, complete projection and native publication tests remain unrun.
- Continue independent supported Phase 1 tests, then six real Phase 2 test
  binaries and Phase 3 tests, alongside remaining Phase 3/4 module/product builds.
  Qualified Phase 2 test binaries: 0/6. Full Phase 3/4 and speedup are unverified.
- Request 40 build jobs, record actual admission, reuse valid caches, and retry
  only changed failures. Do not replay green or closed three-cycle lanes.
- Source/perf fixes land only after their applicable gates; this is a plan update.

The supplied SIMD/GPU/Sosix design remains unavailable and is not substituted.
See [implementation plan](incremental_build_tldr_scv_implementation_2026-10-10.md)
and [acceptance matrix](../sys_test/incremental_build_tldr_scv_acceptance_2026-10-10.md).
