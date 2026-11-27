# Phase 3 must fail when the HIR warm-up pool degrades to serial (2026-11-13)

Since the coordinator degrades a pre-spawn HIR pool refusal to serial HIR
(`src/app/cli/native_build_main.spl`, `native_build_hir_refusal_runs_serial_v1`),
a refused pool no longer fails the build. It prints
`[hir-shard] WARNING: HIR warm-up pool refused before any worker started (...)`,
lowers HIR serially in the final worker, and continues into the MIR workers
with a cold HIR cache. Phase 3 must build in parallel on at least 2 cores, so
that warning must not pass silently there.

- [ ] Bootstrap verifier: fail the Phase 3 (Stage 3) build, and the Phase C
  tool rows it gates, when its log contains `[hir-shard] WARNING` (serial
  HIR), naming the refusal reason from that line. Phase 2 rows may keep the
  warning advisory. Pin it with a contract test fixture log containing the
  warning (must FAIL) and one without it (must PASS).
