# Borrow check retains ~21-24 MB per module: no transient scope (2026-10-24)

Bug id: `borrow_check_unscoped_rss_growth_2026_10_24`
Related: `mir_phase_rss_retention_2026_10_24.md` (left this OPEN),
`borrow_loan_work_budget_exhausted_2026-10-24.md` (separate follow-up).

## Symptom
RSS grows by about 23 MB for every module the borrow checker visits, and none of it
comes back. At 1471 modules that is about 30+ GB on top of the ~40 GB post-MIR baseline,
and this is what OOMs Phase 3.

## Attribution (current producer, 204-module probe `pa.spl`, run-pa-after)
- `mir_verify` runs inside the MIR phase. Its last module, `idx=203 done`, is at +287154 ms,
  the same instant as `aot:lower_to_mir:done`.
- `aot:borrow_check:start` is at +287155 ms. Borrow check ends (`state=failed`, 6 work-budget
  failures) at +306551 ms, so it runs for 19.4 s.
- The MIR worker RSS is flat at 3629 MiB until borrow check starts. It then climbs
  3629 -> 4360 -> 4879 -> 5379 -> 5889 -> 6450 -> 7198 -> 7644 -> 7939 -> 8356 MiB, sampled
  every 2 s across the ~19 s borrow window.
- Total: +4.7 GB over 203 modules = ~23 MB/module, all inside the borrow window.
  Verify contributes ~0.
- Re-run on 2026-10-24 with the p2shard-3 producer:
  - Settings: 1 s sampling, `SIMPLE_BORROW_WORK_BUDGET=20000000`, `SIMPLE_SCV_FREEZE_FALLBACK=1`,
    14G cap. Launcher: `scratchpad/mirmem/mb.sh`, run dir `run-pb-before`.
  - Borrow check started at +254239 ms and finished at +290346 ms (`aot:borrow_check:done`,
    36.1 s). All 202 modules succeeded, so this run has no budget failures.
  - Worker RSS was flat at 3630 MiB until the window opened. It then rose linearly to
    10181 MiB in ~36 s, matching the window, and stayed flat at ~10230 MiB afterwards.
  - Total: **+6.55 GB / 202 modules = ~32 MB/module**. The earlier run's ~23 MB was lower
    because 6 modules aborted on the budget.
  - Codegen then added more on top, and the 14G cgroup OOM-killed the run (rc=143). That is
    unrelated to this attribution.

## Cause
`CompilerDriver.borrow_check` (`src/compiler/80.driver/driver_pipeline_passes.spl:27,41`)
calls `check_mir_module` (`55.borrow/borrow_check/mod.spl:835`) directly, with no transient
scope. The runtime is no-GC: an allocation is reclaimed only by `rt_transient_array_scope_end`.
So every `BorrowChecker`, CFG, `NLLChecker`, `points` / `before` / `after` liveness dict and
`[i64]` push-copy (`nll.spl:700-765`) is retained for the life of the process.

MIR lowering does this right. It runs each module in its own scope and promotes only the
`MirModule` (`50.mir/_MirLowering/module_lowering.spl:2287-2423`). Its own warning says an
unscoped module "retains its whole lowering arena". Borrow check was the per-module
MIR-phase pass that lacked that scope.

Whether `module.functions[symbol]` / `MirBody.from_function` copy the body no longer matters
under scoping: copy or reference, it dies at scope end.

## Fix
`borrow_check_module_scoped_v1(name)` (same file):
1. Begin a scope.
2. Run `check_mir_module`.
3. Pause the scope and promote only the `[NLLError]` list.
4. End the scope.

If the scope is refused (an outer scope is live) or the promotion fails, the module is
re-checked unscoped. In that case it prints `[borrow-scope] WARNING ...`, the verdict stays
the same and RSS behaves as before.

The check reads the already-promoted MIR and writes no shared state. `55.borrow` has no
globals and calls no `mir_data` registry setters. So the verdicts are unchanged.
The NLL data structures are untouched. The O(n^2) liveness sets stay as the budget bug.

## Expected
About 21-32 MB/module saved: the only retained item is the error list. That is about
30+ GB at 1471 modules. One large module still peaks inside its own scope. This fix bounds
the *cumulative* retention, not the single-module peak.

**AFTER numbers are PENDING a Stage 2 rebuild.** The fix lives in the compiler source, and the
current producer is prebuilt. After the rebuild, any `[borrow-scope] WARNING` line means
scoping is being refused and the saving is lost.
