# Phase Ladder linux-x86_64: phase 1->2 fails with stage1 SIGSEGV in HIR (not OOM)

- Date: 2026-11-26
- Status: open
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
