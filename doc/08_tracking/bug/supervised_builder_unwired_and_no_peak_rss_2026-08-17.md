# Supervised builder: not yet wired to a front end, and peak RSS is always 0

- **Filed:** 2026-08-17
- **Status:** OPEN
- **Domain:** compiler / driver
- **Severity:** P2

Tracks the parts of `doc/02_requirements/compiler/supervised_builder.md` that
`ParallelBuilder.build_supervised()`
(`src/compiler/80.driver/driver_build/parallel.spl`) does **not** yet satisfy.
The mechanism exists and is unit-verified; these are the gaps between it and the
requirement, stated rather than left to be discovered.

## Gap 1 — R8: no front end calls it (the important one)

`build_supervised()` has **zero callers in `src/`**. Both entry points named by
the requirement still use the in-process paths:

- `driver_aot_native_output.spl` calls `ParallelBuilder` via `build()` /
  `build_parallel()`, and constructs its config with
  `ParallelBuildConfig.default()` — for which `unstable` is `false`.
- the bootstrap path does not construct `ParallelBuildConfig.bootstrap()`
  anywhere yet.

So `ParallelBuildConfig.unstable` and `unit_timeout_ms` are currently *declared
and honoured by the supervisor*, but nothing selects the supervisor. Until a
front end branches on `config.unstable`, a real build still dies with its worker.

This lane owned exactly one file (`parallel.spl`) and
`driver_aot_native_output.spl` is owned by another lane, which is why the wiring
is filed rather than done. The wiring is a branch at the fan-out site:
`if config.unstable: builder.build_supervised(...) else: builder.build_parallel(...)`,
plus failing the link closed on `outcomes.all_ok() == false` and printing
`outcomes.summary()`.

## Gap 2 — R5: `peak_rss_kb` is always 0

`BuildUnitOutcome` carries `peak_rss_kb` and `attribution_line()` prints it, but
`build_supervised()` passes `0` at every construction site. There is no
`rt_process_*` primitive exposing a child's `ru_maxrss`; `wait4(2)` /
`getrusage(RUSAGE_CHILDREN)` are not surfaced to Simple. Wall time (`wall_ms`) IS
recorded and is real, so the "which file is slow" half of R5 works; the "which
file is fat" half does not. Reporting 0 is deliberate — inventing a number would
be worse — but a reader should know it is a placeholder, not a measurement.

## Gap 3 — R6: no resume

`build_supervised()` attempts every unit every time. Skipping units already `OK`
needs the per-unit interface digest that `action_key.spl:197-204` implements and
nothing calls; the current `cache_scope_root` hashes the whole loaded source
closure, so one edit drops reuse to zero. Unchanged by this work, restated here
so the supervised path is not mistaken for incremental.

## Gap 4 — acceptance fixture not built

The requirement's acceptance criterion is a six-module fixture compiled in ONE
run. What exists instead is the unit-level proof: real children that really die
by SIGSEGV / SIGKILL / SIGTERM, plus a timeout and a missing-artifact case, in
`test/01_unit/compiler/driver/supervised_build_survives_worker_death_spec.spl`
(4 examples) and
`test/01_unit/compiler/driver/supervised_build_outcome_class_guard_spec.spl`
(5 examples). Both include the requirement's negative control by ablation: with
`parallel_supervised_argv()` reverted, 2 of 4 examples go red. The end-to-end
fixture over real `.spl` modules waits on Gap 1.

## Also filed separately

`doc/08_tracking/bug/rt_process_wait_discards_signal_number_2026-08-17.md` — the
runtime folds every signal death to -1; the supervisor works around it with a
shell interposition that costs one extra fork+exec per unit.
