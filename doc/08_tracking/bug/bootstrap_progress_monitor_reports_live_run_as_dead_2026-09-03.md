# bootstrap-progress.log reports a LIVE, fully-working run as dead
**Date:** 2026-09-03

Status: fixed 2026-09-21

## Resolution

`bootstrap-progress-watch.shs` now selects a single-snapshot `ps` backend when
`/proc/<pid>/stat` is unavailable. It reconstructs the descendant and process
group sets from PID/PPID/PGID, sums RSS in KiB, and differences cumulative CPU
time between samples. Each CPU baseline is bound to the process `lstart` birth
identity so PID reuse cannot inherit prior work. An unreadable snapshot or one
missing the watched root emits unknown metrics plus a scan miss and does not
write baseline state. Linux retains the existing procfs implementation.

The portable regression starts a sleeping shell with a live child and requires
exactly two tree members, positive child-inclusive RSS, and distinct root RSS.
It runs on Darwin without Linux's unsupported `ps --ppid` option. The test
also deterministically covers snapshot failure, a busy child CPU delta, PID
reuse, process-group membership, and exclusion of the nested watcher subtree.
It passed on macOS arm64 with the pre-fix zero-process path replaced.

## Symptom

`build/bootstrap/bootstrap-progress.log` emitted, every 30s for over an hour:

```
status=alive-no-progress ... cpu_pct=0.0 rss_kb=0 tree_cpu_pct=0.0 tree_rss_kb=0
tree_processes=0 top_pid=none top_rss_kb=0 tree_scan_misses=0
stall_streak=155 phase=source_closure done=763 total=763 tasks_done=1 tasks_total=6
```

Every liveness field reads dead: no processes in the tree, no CPU, no RSS, a
stall streak of 155 consecutive samples.

## Ground truth: the run was perfectly healthy the whole time

```
PID   STAT  TIME      RSS     ELAPSED   COMMAND
19435 SN    0:18.22   123872  01:21:50  .../simple      (parent, sleeping on child)
19461 SNs   0:00.05   608     01:21:47  timeout --kill-after=10s 7200s
19462 RN    70:07.86  141552  01:21:47  .../simple      (worker, RUNNING)
```

pid 19462 was in state `R` with **70 minutes of accumulated CPU**. Sampled twice
45s apart: `70:24.55 -> 71:08.59` — 44s of CPU in 45s of wall clock, i.e. a
saturated core. RSS climbing 141MB -> 154MB. It was in phase 3, doing exactly the
HIR lowering work it was supposed to be doing.

`tree_scan_misses=0` makes this worse: the sampler reports *zero misses* while
finding zero processes, so it is confidently wrong rather than degraded.

## Cost

Acting on the monitor, this run was declared dead and its wrapper chain killed
(`pkill -f bootstrap-from-scratch`). The worker survived only because the pkill
pattern did not match the `simple` binary itself. A relaunched chain then failed
with:

```
error: timed out waiting for bootstrap output ownership: .../s3-wt/build/bootstrap
```

which was the **correct** behaviour — the ownership lock did its job and refused
to let a second chain corrupt the live run's output dir. That refusal is what
exposed the misdiagnosis.

## Contributing trap: the polled log path does not exist

The stage-3 compiler writes stderr to
`build/bootstrap/stage3/<triple>/stage3-tmp/simple_err_<pid>_<ts>.txt`, not
`stage3-native-build.log` / `native-build-stderr-*.log`. Polling the latter
returned "no log yet" for an hour while a 507KB log sat at the real path. Its
last write (18:25, end of `phase2:surface`, `seq=763`) is when phase-3 output
stopped being chatty — not when the process stopped.

Combined, the two produced a confident, entirely false "the run is dead" reading
from two independent-looking sources.

## Required fixes

1. A sustained `tree_processes=0` must never be reported as `alive`. Either the
   scan is authoritative — in which case 0 processes is terminal — or it is not,
   in which case it must report `unknown`, never `alive-no-progress` with
   fabricated `cpu_pct=0.0 rss_kb=0` numbers.
2. `tree_scan_misses` must count the case "expected to find the worker and did
   not". It read 0 while missing every process.
3. The monitor should track the worker pid, not only the wrapper's.
4. Any liveness check must read the phase log at the path the compiler actually
   writes, and cross-check `ps` CPU-time deltas before declaring a stall.

## Rule of thumb this establishes

A stall verdict needs a **CPU-time delta over an interval**, not a status field.
`ps -o time= -p <pid>` sampled twice, 45s apart, settled in one command what the
monitor got wrong for 155 consecutive samples.
