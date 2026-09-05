# Supervised builder: not yet wired to a front end, and peak RSS is always 0

- **Filed:** 2026-08-17
- **Status:** OPEN (all four gaps re-confirmed 2026-08-17 by an independent lane —
  see *Re-confirmation* at the bottom; no code change made)
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

## Why Gap 1 is not a one-line wiring change (investigated 2026-08-17)

Appended by the `driver_aot_native_output.spl` owner after attempting the wiring.
The branch itself is trivial — `if config.unstable: build_supervised(...)` — but
`build_supervised` requires `spawn_fn(path) -> pid`, **a child process that
compiles ONE module**, and no such entrypoint exists.

What exists instead:

- `src/app/cli/native_build_worker.spl`, spawned by
  `run_native_build_worker` (`native_build_main.spl:246`), is a worker for the
  **whole build**, not per module. There is no `--module` / `compile-one`
  surface anywhere in the native-build CLI (grepped: no `compile-one`,
  `compile_one_module`, `single-module`, or per-module `--module` flag).
- The in-process compile the driver actually calls,
  `_compile_frozen_module_capsule(capsules, ...)`, works from
  `FrozenNativeModuleCapsuleBatchV1` — **in-process state**. It is frozen for
  identity checking, not serialized for transport, so a child cannot be handed
  one.

So a per-module child would today have to re-load the entire compiler graph
before compiling its single module. On the ~600-module bootstrap that is a
per-unit cost measured in minutes (a cold fixture build of THREE trivial modules
spends ~5 minutes in `load_sources` alone under the interpreter), i.e. the naive
wiring is not merely slow but unusable.

The real prerequisite is therefore one of:

1. a `compile-one-module` entrypoint whose child can reconstruct just the state
   that module needs — which is what a persisted capsule (`.smf`-style) would
   buy, and note `SmfManifest` is written but never verified on load; or
2. `fork()` after the frontend completes, so each child inherits the already-built
   module graph and pays no reload. This fits the existing shape best — the
   driver reaches codegen with everything in memory — but needs a fork surface
   the runtime does not currently expose.

Until one of those lands, `build_supervised` is correct, unit-proven, and
unreachable from a real build. **Do not "fix" this by having the driver call
`build_supervised` with a `spawn_fn` that re-runs a full build per module** —
that trades a crash-safety gap for a runtime blowup and would look green in a
3-module fixture while being unusable on the bootstrap.

What IS wired and verified today: outcome accumulation and record-and-continue
in `driver_aot_native_output.spl` (`0c9d671fcd59`), so an in-process build now
reaches the end of the module list and names every bad module in one run. That
covers a compiler ERROR; it does not survive a worker SIGSEGV, which is exactly
what Gap 1 still owes.

## Re-confirmation 2026-08-17 (independent lane, no change made)

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
size 59537240, mtime 2026-08-17 12:58:51 UTC (Rust bootstrap seed).

```
$ grep -n "build_supervised\|peak_rss_kb" src/compiler/80.driver/driver_build/parallel.spl
399:        # as a crashed spec reported as a pass. `build_supervised()` is the real
693:    me build_supervised(spawn_fn: any, artifact_fn: any) -> BuildOutcomeSet:
$ grep -rln "build_supervised" src/compiler/80.driver/driver_build
./parallel.spl
```

Gap 1 stands: the only occurrences of the name are its own definition and a
comment. Gap 2 stands: `peak_rss_kb` appears only in `build_outcome.spl`
(:128 field, :132/:150 params, :143 the always-0 construction, :176 the print) —
no producer measures it.

Gap 2 is additionally blocked for this lane by its HARD LIMITS: surfacing a
child's `ru_maxrss` needs a new `rt_process_*` primitive in the C/Rust runtime,
which cannot be picked up without a bootstrap. Deliberately not attempted.
Gaps 1, 3 and 4 are unchanged, and the "do not wire `spawn_fn` to a full
rebuild" warning above still applies.
