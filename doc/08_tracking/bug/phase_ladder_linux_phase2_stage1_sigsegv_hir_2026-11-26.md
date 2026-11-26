# Phase Ladder linux-x86_64: phase 1->2 fails with stage1 SIGSEGV in HIR (not OOM)

- Date: 2026-11-26
- Status: open (diagnostics landed; one phase-1 blocker fixed, verification-pending; phase 2 still unproven)
- Severity: P1 (blocks every Phase 3+ RC, so Whole Test Lanes refuses to run)
- Lane: `.github/workflows/phase-ladder.yml` -> `phase-ladder-rung.yml`, `rung1 / rung 1 linux-x86_64`, GitHub-hosted `ubuntu-24.04` (16 GB RAM)

## Summary

The working hypothesis was that phase 1->2 runs out of memory on the hosted
runner. The newest release/1.0.0 evidence does not support that. The phase-2
build by the freshly built `build/bootstrap/stage1/simple` crashes with
**SIGSEGV** early in HIR, with plenty of RAM and swap still free. Lowering job
counts or adding swap will not fix it. No workflow change was made.

## Evidence

Run 45659415417 (push, release/1.0.0, source `9421fbdbaddee3e7f65c4a823b78d0525f47f9ea`),
job 139369796191, artifact `bootstrap-ladder-diagnostics-linux-x86_64-r1`, `evidence/step.log`:

```
[hir-shard] admission worker estimate=4026254 kB (coordinator peak 2110264 kB reserved for the coordinator only)
[build] phase=hir ... done=480 total=1629 ... cached=0 failed=0 ... elapsed_ms=635432 current=lib.nogc_sync_mut.io.thread
error: native-build worker terminated with signal 11 (SIGSEGV) before producing a binary; NOT a compile failure.
Phase 2 build with .../build/bootstrap/stage1/simple failed (rc=117); falling back to the Rust seed
phase-ladder: phase 2 build failed
```

- Step wall time 16 min. Crash after 635 s, at HIR module 480 of 1629.
- Resources at that point: `Selected build jobs: seed=4 selfhost=1`, swap step
  `swap_gib=53`, 15 GiB RAM. Coordinator peak about 2.1 GB, worker estimate
  about 4 GB. The documented 36-40 GB peak
  (`native_build_per_worker_baseline_rss_2026_10_24.md`) is at MIR start, far
  past this point.
- No exit 137, no "Killed", and no runner loss on this attempt. The worker got
  signal 11, not SIGKILL.

## Secondary and older signals (do not explain the current failure)

- Run 45547756300 (2026-11-25 04:35, older source): linux-x86_64 rungs 1-3
  (jobs 138981456655, 139045730187, 139119066445) and riscv64 rung 4 ended with
  "The hosted runner lost communication with the server" about 78 min into
  "Climb one phase". That looks like memory starvation, but the jobs left no
  logs, so the phase cannot be confirmed. The newer source crashes before it
  gets that far.
- Run 45659415417 rung2 linux-x86_64 (job 139481952559): exit 143 after
  172 min. All post-steps were skipped, so there are no artifacts. The cause is
  unknown. It was not the 340-minute job timeout.
- Run 45684271709 (main, schedule): exit 1 ten seconds after "No previous
  compiler qualified; using the Rust seed". That is a different branch and a
  different failure.
- `slow-rung*` "success" rows for linux-x86_64 only mean the lane was not
  selected. slow-rung runs `darwin-x86_64` only.

## Next steps

1. Reproduce locally: build the stage1 compiler at `9421fbdbadd`, then
   native-build phase 2 with `selfhost=1`. Capture a core and backtrace at or
   near `lib.nogc_sync_mut.io.thread`, the HIR module that was in progress.
2. Check whether the crash is deterministic: same module, `cached=0`. Also
   check stack depth (worker thread stack size) against null-deref.
3. Make the ladder keep `/var/crash` or core files in the diagnostics artifact,
   so the next CI crash carries a backtrace.

## Update 2026-11-26 (lane segv12)

- **Diagnostics landed (PR #11845, merge `c91663afb69`).** On linux lanes the
  rung now installs gdb, sets `core_pattern` to `build/ladder/cores`, and runs
  the Climb step under `ulimit -c unlimited`. On failure it writes
  `evidence/backtraces/<core>.bt.txt` (`thread apply all bt full`) into the
  diagnostics artifact. No gate changed.
- **Run 45736111889** (linux-x86_64 only, max_rung=1, branch at 15b1bbe7): no
  qualified compiler was found, so phase 1 was built with the Rust seed and
  failed before phase 2. Only `hir_match_coverage.spl` failed:
  `cannot infer field type while lowering walk_expr: struct 'ANY' field
  'sites'`. That came from 3968df8e894, which retired the
  `walk_hir_expr<MatchSiteScan>` workaround. No core was written because
  nothing crashed.
- **Fix PR #11850 (merge `6eaf8fc945f`) restores the annotation.** It is
  verification-pending. Run 45739034803 then got **rung 1 linux-x86_64 to
  success** (phase 1 built).
- **Run 45739034803 rung 2** (job 139647914474, phase 2 by stage1): the log
  stops at 02:32:25 in HIR, module 291 of 1630, with no error line. The
  annotation is "The hosted runner lost communication with the server". Every
  post-step was skipped, so there are no artifacts and the job log cannot be
  fetched. This is the same signature as run 45547756300 and rung 2 of
  45659415417: the runner VM dies (most likely memory or swap starvation of
  the 16 GB host with 53 GiB swap). It is not a process SIGSEGV, so a core or
  gdb backtrace cannot be captured this way.
- **Still open:** the module-480 SIGSEGV has not recurred under diagnostics,
  and phase 2 has not passed. Next steps:
  1. Add an in-job RSS/`/proc/meminfo` sampler that writes to the step log
     and kills the build (rc!=0, a loud failure) before the VM starves, so the
     artifact steps still run.
  2. Rerun phase 2 at a lower `selfhost` thread count to tell starvation
     apart from the SIGSEGV.

## Update 2026-11-26 (lane hirmem): local phase-2 memory profile, HIR is NOT memory-bound

- **Setup.** Same program and source as rung 2 of run 45739034803: the rung-1
  artifact `ladder-linux-x86_64-r1` (`linux-x86_64-p1/simple`, pure-Simple
  stage1) building source `d4ea18fa337` with the exact
  `build-next-phase-ci.shs` command (`--low-memory --threads 2`, same env).
  Run on a WSL2 Ubuntu VM (63 GB, 80 vCPU) with the source on tmpfs. Every 5 s
  the run sampled `/proc/<pid>/VmRSS` for each process in the build's process
  group, with a kill switch at 24 GB.
- **Result (678 samples, about 56 min, killed by hand while MIR/objects were in progress):**

  | point | tree RSS | coordinator | per-file workers |
  |---|---|---|---|
  | load_sources/parse | 2.06-2.36 GB | 1.46-1.49 GB | 2 x ~300 MB |
  | HIR 278/1630 (peak in HIR) | 2.25 GB | 1.50 GB | 301 + 403 MB |
  | HIR 314/1630 (past CI's 291) | 2.15 GB | 1.50 GB | 2 x 300 MB |
  | whole-run peak (native_compile) | **2.41 GB** | 1.51 GB | 301 + 544 MB |
  | +56 min, 134 objects | 2.18 GB | 1.51 GB | 2 x 300 MB |

- **What grows:** almost nothing. Workers are short-lived processes, one per
  16-module unit. They exit, which frees their memory, so there are no N
  retained worker copies. The coordinator creeps about 1 MB/min
  (1460 -> 1512 MB). That is not a session-cache blowup. There is no
  per-module retained HIR in the coordinator. On-disk state is small (cache
  372 MB, TMPDIR spool 3 MB, `build/scv` 235 MB).
- **Conclusion:** at `--threads 2`, phase 2 needs about 2.4 GB, roughly 15% of
  the 16 GB runner. Memory starvation by the build tree does not explain the
  runner loss at module 291, so no retention fix was made. A job-count
  reduction is **not** warranted: 16 GB would fit about `(16 - 1.5 OS - 1.6
  coordinator) / 0.55 = 23` workers by RSS. A lower thread count is not the
  lever. Caveat: the admission estimate printed by the compiler (`worker
  estimate=6291456 kB`) is about 15x the measured worker RSS, so it is very
  conservative.
- **Proposal to the CI-sampler lane:** look at non-RSS causes of the VM loss.
  Candidates are disk exhaustion from the 53 GiB swapfile on the runner disk
  plus caches, the runner agent being starved of CPU or I/O, and the SIGSEGV
  path. The sampler should also log `df` and the swap fill level, not only RSS.
- **Local-run gotchas (in case this needs reproducing):** SCV refuses a checkout whose `.git` points at
  a Windows path (`git-event-source-unavailable`), and a 9p git walk fails
  (`git-event-refresh-failed`). The workers also need a writable `TMPDIR`.
