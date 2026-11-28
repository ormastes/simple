# Every per-file unit child replays the whole preclosed alias walk (2026-11-28)

Status: verification-pending (fix default ON; native wall-time/RSS after-run needs a Stage 2 binary built from it)

## Symptom
Stage 2 full-CLI build, per-file worker pool (`[file-worker] unit picked=16`). Every 16-module unit
spends 91-104 s in `phase=load_sources` before it picks anything (14 of 14 units in
`pinned-41e537bc54c6/compiler_cli_build.log`), then ~30 s in the surface sweep, ~16 s in HIR and
~17 s in MIR + objects. 4225 modules at 16 per unit is ~265 units, so the load alone is ~6.8 h of a
single worker's time.

## Root cause
- A unit is one fresh process: `NativeFileUnitProcessInvokerV1.run_unit`
  (`src/app/cli/native_build_main.spl:3667`) spawns `--hir-shard` per unit. The pick runs only
  after the full load (`driver_source_parse_streaming.spl:203-228`).
- That process loads the whole frozen selection through `load_sources_impl`
  (`driver_orchestration.spl:315`). Reading and digest-checking the 4220 selected files is cheap.
- The cost is `driver_preclosed_source_aliases_v1`
  (`driver_source_pipeline_loading.spl:1416`): it re-scans the imports of every admitted source and
  re-resolves each (importer directory, spec) through the filesystem resolver, only to append alias
  rows (about 4300 rows in, 7240 out) that are identical for every consumer of one selection.

The surface phase is not the cause: per unit it parses only the unit's closure (44 files) and prints
`surface:file:released` for the other 4225.

## Measurement (standalone unit child, phase profile)
Binary: admitted Stage 2 compiler, sha256
`c7c151462a203bc700d3793c65e917b6df0119efa54a058dccf486c3707b05a0`, 124542144 bytes, built from
`38cb1016a31f`; sources `bf9f1968949` (release/1.0.0); aarch64, 12 GiB cgroup cap.

| Point | Process time | Process RSS |
|---|---|---|
| `compile:start` | +2.5 s | 0.43 GiB |
| `load_sources:preclosed:admitted` (2 inventory reads, visibility maps) | +13.3 s | 0.88 GiB |
| `load_sources:seeded` (4220 files read and digest-checked) | +16.4 s | 1.50 GiB |
| alias walk, still running | +79 s | cgroup at the 12 GiB cap, OOM-killed |

The walk did not finish under the cap, so its duration is "more than 63 s" here; the production log
puts the whole load at 91-104 s, which leaves ~75 s for it. The cgroup figure is not process RSS.

A smaller selection completes under the cap and isolates the walk (same binary, a 662-source
entry closure, 762 rows in, 1059 out):

| Point | Process time | Process RSS |
|---|---|---|
| `load_sources:preclosed:admitted` | +13.8 s | 0.81 GiB |
| `load_sources:seeded` | +14.5 s | 0.88 GiB |
| `load_sources:bulk:done` (alias walk finished) | +23.0 s | 2.29 GiB |
| `load_sources ... complete` | +25.3 s | 2.47 GiB |

The walk is 8.5 s and 1.4 GiB there, a third of the load and most of its memory. That child also
spent 19 s of wall time before `compile:start`.

A native probe that calls the new index code could not be built: its 662-module closure includes
the compiler's HIR modules, and one unit's HIR lowering reached the 12 GiB cap (13 of 42 units done).

Recipe: run the coordinator with `SIMPLE_COMPILER_PHASE_PROFILE=1 SIMPLE_PHASE_RSS=1` and its own
`--cache-dir`, copy the first unit child's `/proc/<pid>/environ` and `cmdline`, stop the
coordinator, drop `SIMPLE_NATIVE_WORKER_CHILD_PARENT_PID`, and re-run that child alone under
`systemd-run --user --scope -p MemoryMax=...` with timestamped output.

## Fix
`src/compiler/80.driver/driver_preclosed_alias_index_v1.spl`: the first consumer with a HIR queue
publishes the alias rows to `<hir_queue>/preclosed_alias.idx`; later consumers rebuild the same rows
with zero import resolutions. Same shape as `unit_order.idx`
(`unit_child_admission_scans_whole_closure_2026-11-15.md`). Default on;
`SIMPLE_PRECLOSED_ALIAS_INDEX=0|false|off` rolls back. The build log now says which path ran:

```
[preclosed-alias] index miss reason=preclosed alias index absent rows=<n> aliases=<k> published=true
[preclosed-alias] index hit rows=<n> aliases=<k> resolutions=0
```

Spec: `test/01_unit/compiler/driver/preclosed_alias_index_spec.spl` (second consumer adds zero to
`driver_preclosed_alias_resolution_count_v1()` and returns field-identical rows; content, order,
roots, truncation, switch-off and no-queue all fall back to the walk).

## Acceptance run still owed
A Stage 2 binary built from this change, same recipe: the second unit's `load_sources` should drop
from ~92 s to ~20 s with `index hit` in its log, objects and cache keys unchanged, and its RSS at
`load_sources ... complete` should be near the 1.5 GiB seeded figure.

## Not fixed here
- The first consumer, and any consumer without a HIR queue (parse-shard workers, the coordinator's
  own load), still runs the walk: more than 63 s and more than 10 GiB of growth for 4220 sources.
  The walk itself is the defect; the index only stops it repeating.
- Each unit still pays ~14 s of request admission (two full inventory reads of 47,515 rows at
  ~5.7 s each, plus the visibility maps), ~3 s of file reads, two more inventory reads after HIR
  (10.4 s) and the ~30 s surface sweep that visits all 4225 sources to release them.
- A worker still starts one process per unit; the source tree is not held across units.
