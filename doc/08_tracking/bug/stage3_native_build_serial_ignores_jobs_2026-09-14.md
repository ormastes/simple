# Stage-3 bootstrap native-build ignores --jobs/--threads: measured single-core at real 14,340-file scale (2026-09-14)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN — **not a new root cause**, a bootstrap-scale confirmation of an
  already-located defect. Handover to a perf lane; the user wants the
  bootstrap to use at least 15 of this host's 20 cores.
- Area: `src/compiler/80.driver/driver_build/parallel.spl` (`ParallelBuilder.build()`),
  `driver_aot_native_output.spl`, `src/app/io/_CliCompile/native_build.spl`
- Found by: BOOT-18, running the receipt-free diagnostic Stage 3
  (`native-build --entry src/app/cli/bootstrap_main.spl --source src/compiler
  --source src/app --source src/lib --entry-closure`) against a real,
  Linux-aarch64-ADMITTED Stage-2 candidate, `--threads 16` on a 20-core host at
  load ~3-6.

## Same defect as two already-OPEN records — read those first for the root cause

- `doc/08_tracking/bug/native_build_step5_serial_threads_ignored_2026-09-04.md`
  (OPEN) already root-causes this exactly: `ParallelBuilder.build()`
  (`parallel.spl:389`) has two branches and **both are sequential** — the
  "parallel" branch (`:480-521`) chunks the ready set into groups of
  `max_workers` but then runs a plain `while chunk_idx < chunk_end: compile_fn(...)`
  loop with **no spawn, no thread**, so `--threads`/`--jobs` only moves a chunk
  boundary. The real process-spawning implementations, `build_parallel()`
  (`:553`) and `build_supervised()` (`:697`), have **zero callers** because
  `compile_fn` closes over in-memory frozen MIR capsules that cannot cross a
  process boundary without a one-module compile CLI — tracked as
  `doc/03_plan/infra/unstable_mode_build_side.md`. That doc also states the
  MIR-lowering phase (step 4/6, `driver_pipeline_lowering.spl:262-311`) is
  serial for an independent reason: it shares one mutable `MirLowering` whose
  `.symbols` field is reassigned per module.
- `doc/08_tracking/bug/native_build_phases_after_parse_single_threaded_2026-08-22.md`
  (marked RESOLVED for the parse-shard half only) measured the same shape
  earlier: parse can shard across worker processes, but HIR/typecheck/mono/MIR/
  codegen/link all run "in the one driver process, one module at a time."

This record does not re-derive either root cause. What it adds: a measurement
at the actual scale that matters for the bootstrap wall clock — the full
`bootstrap_main.spl` entry-closure (14,340 files under `--source src/compiler
--source src/app --source src/lib`), not a 102-unit MCP-server build or a
192-module lint closure — plus fresh `ps` evidence that the *whole process*,
not just one phase, stays at one OS thread for as long as this lane observed
it (through the parse phase and load).

## Measurement

Host: aarch64 Linux, 20 cores (`nproc`), load average 3.46-5.9 at start (idle
per the coordinator's own read of the host). Stage-2 admitted candidate:
`build/bootstrap-boot18b/stage2/aarch64-unknown-linux-gnu/simple`, 152345176 B,
sha256 `babd73a74bc8e0ca5e56e8df532aeeab6013e53b…`. Invocation (from
`scripts/bootstrap/bootstrap-from-scratch.sh`'s own Stage-3 argv shape,
replayed receipt-free):

```
<stage2-candidate> native-build --target aarch64-unknown-linux-gnu \
  --backend llvm --runtime-bundle core-c-bootstrap \
  --source src/compositions/kernel_llvm_cranelift \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 16 --mode dynload \
  --entry src/app/cli/bootstrap_main.spl -o <out>
```

`SIMPLE_NATIVE_BUILD_THREADS=16`, `SIMPLE_BOOTSTRAP=1`,
`SIMPLE_BOOTSTRAP_STAGE3=1` all set (from the bootstrap engine's own Stage-3
env vector, per its transcript) — `native_build_should_use_worker()`
(`src/app/cli/native_build_main.spl:219-229`) is documented to trigger worker
mode on `SIMPLE_BOOTSTRAP` alone, so this run is not missing that opt-in.

`ps -o pid,pcpu,nlwp,etimes` and `pstree -p` on the compiler PID, twice:

| elapsed | pcpu | nlwp (threads) | child processes (`pstree -p`) | last log line |
|---|---|---|---|---|
| 24 s | 99.3% | **1** | 0 | `phase2:surface:file:parse-start ...gzip/header.spl` (early) |
| 83 s | 99.6% | **1** | 0 | `phase2:surface:file:parse-start ...mir_opt/pattern/rules_clib_parity.spl` |

`ps -L -o pcpu -p <pid>` thread-level sum matches the whole-process `pcpu`
figure exactly both times (no second thread doing anything, however briefly).
`pstree -p <pid>` shows **zero child processes** at either sample — not even a
parse-shard worker, contrary to what
`native_build_phases_after_parse_single_threaded_2026-08-22.md`'s "resolved"
half would predict for this entry-closure/flag combination; unclear whether
that shard path requires a flag this bootstrap invocation does not pass, or
whether it is scoped differently for `--entry-closure` builds. Not
investigated further here — a fact for the perf lane to check, not asserted
as a new defect.

A background 5-minute-interval sampler
(`scratchpad/boot18/sample_cpu.sh` -> `scratchpad/boot18/cpu_samples.txt`,
this session's scratchpad) continues logging `pcpu`/`nlwp`/`etimes` for the
remainder of the run; anyone picking this up can read that file directly for
the full time series rather than re-deriving it.

## Effect on bootstrap wall clock

Extrapolating from BOOT-16's own Stage-2 measurement in the same family (site
16's receipt: "416 s at 16 jobs vs 423 s at 10 jobs" — i.e. **no speedup at
all** from 10 -> 16 requested jobs on that phase either) and this lane's own
observation that the diagnostic Stage-3 run processed only 832 of 14,340 files
(~5.8%) in 900 s before being cut off by a timeout: on one core, the full
closure is on the order of **hours**, not minutes, for a build the bootstrap
script requests `--jobs=16` for on a 20-core host. This is the concrete cost
the user's "at least 15 cores" ask is about.

## Handover

Not fixed here (perf lane territory per the two existing records' own
scoping, and per the coordinator's explicit routing). Concrete next steps,
already named by the existing records:

1. Wire a one-module compile CLI so `build_parallel()`/`build_supervised()`
   (`parallel.spl:553`,`:697`) have something to `spawn_fn` — the MIR-capsule
   serialization gap `doc/03_plan/infra/unstable_mode_build_side.md` names as
   the blocking precondition.
2. Separately, `driver_pipeline_lowering.spl:262-311`'s single mutable
   `MirLowering` needs to stop being shared across modules before step 4/6 can
   parallelize even in-process.
3. Confirm/deny whether `--entry-closure` bootstrap builds reach the
   parse-shard path `native_build_phases_after_parse_single_threaded_2026-08-22.md`
   describes as fixed — this run's `pstree` showed zero child processes at
   either sample, which that record's "resolved" status does not predict.

## Correction discipline

Per `.claude/rules/vcs.md` "Sync must never clobber": this file is a NEW
record with a name distinct from the two it cites, deliberately, to avoid
repeating the exact stale-snapshot clobber
`native_build_phases_after_parse_single_threaded_2026-08-22.md`'s own
provenance note describes (a docs-sync commit silently reverting a landed fix
+ deleting its record). Nothing in either existing record was edited by this
lane.

