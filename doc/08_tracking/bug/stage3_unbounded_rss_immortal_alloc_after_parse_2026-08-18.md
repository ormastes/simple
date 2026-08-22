# Stage 3 native-build RSS is unbounded: every heap object allocated outside a
# transient parse scope is process-immortal and never freed (2026-08-18)

Status: OPEN (analysis; no build run -- resource embargo, Stage-3 bootstrap live)

## Measured

Stage 3 (`stage2-admitted/simple native-build --threads 2 src/app/cli/bootstrap_main.spl`):
4.4 GB @333s -> 16.4 GB @453s -> 33.8 GB @694s -> 67.4 GB @965s -> killed at
93.0 GB by `kill_simple_monitor` (`rss=93065MB>=90000MB`). An earlier run died at
65.7 GB to earlyoom. RSS PLATEAUS for minutes at 33.8 and 67.4 GB with CPU at
100% and state `R`, then steps. 16.4 -> 33.8 -> 67.4 are successive DOUBLINGS.

## Retention (source evidence, not measured)

In `src/runtime/runtime_native.c` -- the runtime the stage2-admitted NATIVE
binary links -- every Simple-level heap object (string, array, dict, enum,
closure) is entered into `rt_core_immortal_registry` at birth via
`rt_core_register_scoped_immortal` / `rt_core_register_string`. The ONLY path
that ever `free()`s such an object is `rt_core_reclaim_transient_immortal`,
reached exclusively from `rt_transient_array_scope_end`. Objects born outside a
transient scope are, by construction, retained for the life of the process:
"Strings remain process-persistent" (comment at the registry definition).

`/usr/bin/grep -rn rt_transient_array_scope_begin --include=*.spl src/` finds
exactly four call sites:
- `80.driver/driver_source_pipeline_parsing.spl:90`  (phase 2, per file)
- `10.frontend/_FlatAstBridge/module_assembly.spl:949`
- `80.driver/driver_hir_pipeline_lowering.spl:183`   (phase 3)
- `app/check/main.spl:191`

Phase 2 is properly bounded: parse under a scope, project to a compact surface,
`rt_transient_array_scope_pause` -> `module_surface_promote` (promote only the
reachable surface graph) -> `rt_transient_array_scope_end` frees the per-file
parse garbage. That is what the `phase2:surface:file:released path=... seq=N`
events in `stage3-native-build.log` record.

**Phases 4 (MIR), 5 (codegen / LLVM IR emission) and 6 (link) have no transient
scope at all.** Every string and container they allocate while lowering and
emitting 608 modules is registered immortal and is never reclaimed. That is the
monotonic, per-module retention, and it is ~40x the known 2.4 GB interpreted
floor (`native_build_interpreted_worker_fixed_2_4gb_floor_2026-08-18.md`).

The doubling steps with 100%-CPU plateaus are the signature of
`rt_core_immortal_registry` growth: a power-of-two open-addressing table that
`realloc`s and rehashes every entry under a spinlock, holding old + new tables
live across the copy. The table is grow-only -- tombstones are reclaimed on
grow, but the capacity never shrinks.

## Proposed bounded fix (in priority order)

1. **Extend the proven phase-2 discipline to phases 4-5.** Wrap per-module MIR
   lowering and codegen emission in `rt_transient_array_scope_begin/end`,
   promoting only the value that crosses the module boundary -- as phase 2
   promotes only the surface graph. Same mechanism, already load-bearing, and it
   bounds retention to one module's working set.
2. **Stream codegen output per module.** Write emitted IR/object text to disk as
   it is produced and drop the in-memory buffer, so the largest retained
   per-module value is a path.
3. **Registry:** grow in fixed chunks rather than doubling once past a few GB,
   so a rehash never needs old+new of a >16 GB table simultaneously.

## Test requirement -- SPECIFIED, NOT RUN (embargo)

`scripts/check/check-stage3-peak-rss-budget.shs`:
- Runs the stage-3 native-build of `src/app/cli/bootstrap_main.spl`, sampling the
  whole process tree's RSS every 2s from `/proc/<pid>/status:VmRSS`.
- PASS iff the run reaches `phase=link terminal=success` AND peak tree RSS
  < 60000 MB. Verdict line last on stdout, `PASS — peak <n> MB over <k> samples`.
- `ERROR — nothing was checked` exit 2 if no nonzero sample was taken, or the
  process died with rc 137/143/144 (killed != failed).
- NEGATIVE CONTROL: with the phase-4/5 scope calls disabled
  (`SIMPLE_MIR_TRANSIENT_SCOPE=0`), the same assertion must FAIL with peak
  > 60000 MB. Reverted-and-still-green is a broken gate.
- Belongs in the bootstrap lane, never in `bin/simple test`.

## Not verified

No build was run (resource embargo). The retention mechanism is established from
source and from the call-site census above; the attribution of the specific
doubling steps to the immortal registry rather than to a caller-side buffer is
inference from the 2x step pattern, not measurement.

## Fresh canonical evidence (2026-08-22, `codex/session-01a023a8`)

A source-bound four-core Stage 2 build completed and admitted successfully from
commit `d1414723ef0`; the canonical planner-admission-v2 producer then authorized
the required one-thread Stage 3 recovery lane. Stage 3 parsed, promoted, and
released all 687 module surfaces in 458,677 ms, entered HIR, and completed the
first HIR module. RSS rose from 638,492 KiB during late surface parsing to
3,599,144 KiB at HIR 1/687, then to 7,341 MiB. At 13:08:44 UTC, host `earlyoom`
sent SIGTERM because available memory fell below 10%; the compiler exited 143
without a product diagnostic or candidate. The retained log is
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.

This fresh measurement confirms the open blocker on current source: surface
lifecycle is now stable, but HIR retention remains unbounded enough to prevent
Stage 3 admission under shared-host load. Stage 4, deployment, the optimizer,
SPipe/docgen, and bootstrap-ledger PASS publication remain unavailable. The
unblock condition is unchanged: bound the Pure-Simple per-module HIR/MIR/codegen
owner lifetime, preserve behavior/API, and rerun one provenance-bound Stage 3
transaction with the canonical peak-RSS gate.
