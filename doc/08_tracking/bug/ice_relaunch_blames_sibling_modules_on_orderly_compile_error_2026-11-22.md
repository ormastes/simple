# go-to-end relaunch blames sibling workers' modules after an ordinary compile error (2026-11-22)

Status: fixed in `native_build_relaunch_past_ice_crashes` (pure Simple; takes
effect once a producer is rebuilt from this source).

## Symptom

Shard-mode `native-build` under go-to-end. A worker printed
`[first-compile-error] ...` (an unresolved name) and exited with plain status 1.
The parent then reported `worker died ... inside mir_lower of module
lib.scv.maintenance` and `compiler.hir.generated.hir_codec`, re-launched with
both on `SIMPLE_ICE_SKIP_MODULES`, and failed the build regardless. A sibling
worker lowered `scv.maintenance` cleanly in the same run.

## Root cause

`ice_boundary_dead_worker_modules()` (`src/compiler/80.driver/driver_ice_boundary.spl`)
reads every `ice_breadcrumbs.*.log` in the shared run directory. After an
orderly exit the exiting worker has no open crumb, so everything still open
belongs to live siblings. `ice_boundary_attribute_dead_pid_v1` documents this
hazard for the ledger pools; the relaunch path has no worker pid to use it.

## Fix

Exit status 1 with `[first-compile-error]` in stderr returns the first launch
unchanged: no attribution, no skip-list growth, no relaunch. Spec:
`test/01_unit/compiler/driver/ice_go_to_end_crash_supervision_spec.spl`.

## Open

A worker that really crashes while siblings are in flight is still attributed
run-wide; that needs the worker pid threaded into the relaunch function.
