# Light test-daemon lane is slower than the direct lane even after removing all `/bin/sh` spawns from `daemon_lock_alive()`
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN (triaged LIVE 2026-11-11, lane ne13 — 2026-11-05 wakeup fix
  confirmed in source; dominant per-request re-compile term remains, needing
  runtime/verdict-transport support + linux measurement. See addendum.)

## Summary

PERF-5 fixed `daemon_lock_alive()` (`src/app/test_runner_new/test_runner_client.spl`)
to answer the "is the recorded PID alive and is it the light daemon" question
in-process (`file_exists("/proc/<pid>")` + a plain `/proc/<pid>/cmdline` text
read) instead of shelling out to `/bin/sh -c "pid=$(cat ...); kill -0 ...; tr
... | grep -q light_daemon"` via `process_run_timeout`. Measured with a warm,
correctly-identified daemon, this removes all 8 `execve("/bin/sh", ...)`
calls per `simple test <spec>` invocation (see
`test/05_perf/test_runner/daemon_lock_alive_shell_spawn_spec.spl`,
strace logs `warm_before.log` (8 sh execve) vs `warm_after.log` (0 sh execve,
1 total execve) in the PERF-5 receipt).

Despite that fix, the daemon-served lane (`simple test <spec>`, default) is
still measured SLOWER wall-clock than the direct/no-daemon lane
(`--no-session-daemon --no-session-share`) on this shared, heavily loaded
aarch64 host:

| scenario | pre-fix wall (3 samples) | post-fix wall (3 samples) |
|---|---|---|
| default (daemon) | 6.77s / 7.38s / 5.84s | 6.99s / 8.14s / 8.78s |
| `--no-session-daemon --no-session-share` | 1.78s / 1.57s / 0.96s | 3.91s / 3.86s / 3.03s |

Binary: `bin/release/aarch64-unknown-linux-gnu/simple.perf5`, sha256
`3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef`, worktree
`simple-perf-5`, aarch64, shared host with several other agent lanes running
concurrently (load high and non-stationary — these are an envelope, not a
clean A/B; both lanes got slower between the two measurement passes because
of rising host contention, not because of the fix).

## Why this is NOT explained by the shell-spawn fix, and NOT a regression from it

The removed shell-outs cost a proven ~100ms total in a lightly loaded
strace (`warm_before.log`, 8 probes spanning 10:31:19.238 -> .331). That
cannot account for a multi-second gap between the two lanes, before or
after the fix. The daemon lane's own architecture explains the gap instead:

- `light_daemon.spl`'s main loop polls its request directory only every
  **250ms** while idle (`thread_sleep(250)`, `light_daemon.spl:220`), and the
  client separately polls for the response every **100ms**
  (`thread_sleep(100)`, `test_runner_client.spl` `run_one_via_daemon`).
  Both are coarse, uncoordinated polling loops, not a wake-on-request signal.
- The daemon does **not avoid** spawning a fresh process per request: on
  receiving a request it runs `simple run test_runner_single.spl <path>
  --no-session-daemon --sequential --timeout ...` as a brand-new child
  (`light_daemon.spl:140`, inside `handle_request` -> `process_run_bounded`)
  — essentially the same spawn the direct lane performs itself. The daemon
  lane therefore pays a full extra process-spawn (the always-running daemon
  interpreter) PLUS a second nested spawn for the actual work, where the
  direct lane pays only the second one.
- Under CPU contention (confirmed present: several stray `light_daemon`
  processes from OTHER worktrees were observed polling their own request
  directories on this same host during PERF-5's session), coarse polling
  intervals and extra fork/exec calls compound non-linearly rather than
  additively — consistent with both lanes' wall time rising together between
  the "before" and "after" passes above, while the RELATIVE gap (roughly
  4-5x) stayed similar in both passes.

## What was fixed vs what remains open

Fixed (this lane, PERF-5): the literal `/bin/sh` spawn count attributable to
`daemon_lock_alive()`'s 3 call sites is 0, confirmed both by the deterministic
planted-lock pin (`daemon_lock_alive_shell_spawn_spec.spl`, 4 -> 0 sh execve)
and by a real warm-daemon end-to-end strace (8 -> 0 sh execve, total execve
8+ -> 1).

Not fixed here (out of scope for "cut the shell spawns"): the daemon lane
provides no measured wall-clock benefit over the direct lane on this host and
workload shape (a single 1-example spec) — if anything it is consistently
slower. A real fix needs either event-driven request/response signaling
(replacing the 100/250ms polling) or serving the request in-process instead
of spawning `test_runner_single.spl` as a child, and should be measured on an
UNLOADED host to separate the daemon protocol's own fixed cost from this
session's ambient contention.

## Repro

```
rm -rf .build/test_daemon_light
bin/simple test test/fixtures/concurrency/conc_a_spec.spl   # cold, spawns daemon
sleep 1                                                      # let claim_lane() settle + LIGHT_BINARY write
strace -f -e trace=execve -o /tmp/warm.log \
  bin/simple test test/fixtures/concurrency/conc_a_spec.spl  # warm, daemon-served
grep -c 'execve("/bin/sh"' /tmp/warm.log                     # 0, post-fix
/usr/bin/time -f 'wall=%e s' bin/simple test test/fixtures/concurrency/conc_a_spec.spl
/usr/bin/time -f 'wall=%e s' bin/simple test test/fixtures/concurrency/conc_a_spec.spl --no-session-daemon --no-session-share
```


## Update 2026-11-03
No change. The light daemon is bypassed on non-linux; a wall-time budget spec
must be authored and measured on linux. Left open.


## Update 2026-11-05 — polling fixed; per-request worker re-compile remains
Measured on this host (aarch64, shared, phase1 seed binary
`build/phase_snapshots/phase1_1793422538/simple`, worktree
wt-libbug-w6-daemonperf, fixture test/fixtures/concurrency/conc_a_spec.spl,
5 warm samples per lane):

| scenario | before (median) | after (median) |
|---|---|---|
| daemon lane (warm) | 1.47 s (1.33–1.60) | 1.27 s (1.25–1.31) |
| direct lane | 0.68 s (0.62–0.73) | 0.69 s (0.68–0.70) |

A strace of the warm daemon lane showed the doc's "socket setup /
serialization / handshake" notes were only half the story: the daemon's idle
loop called `dir_list(LIGHT_REQ_DIR)` every 250 ms, and `dir_list()` is a
SHELL-OUT — every idle poll was `execve("/bin/sh", ["-c", "ls -1 ..."]) +
execve("/usr/bin/ls")`, ~480 fork/execs per 60 s daemon lifetime. So the lane
had NOT actually reached zero shell spawns; it moved them into the daemon's
poll loop. The client separately polled the response every 100 ms.

Fixed (this lane): wakeup-protocol signaling.
- `run_one_via_daemon()` bumps a wakeup sequence file
  (`.build/test_daemon_light/wakeup.seq`, atomic tmp+rename, content = the
  request id) AFTER the request rename is visible.
- `light_daemon.spl`'s idle loop stat()s that one file in-process every
  10 ms (was: dir_list shell-out every 250 ms); a changed sequence triggers
  one drain of the request dir. A dir_list fallback sweep remains for
  clients predating the protocol: 500 ms cadence until the first wakeup is
  seen, 5 s afterwards (an old client discovering the 5 s sweep withdraws
  within its 2000 ms claim-wait and runs direct — correct, just not
  served). Idle lifetime unchanged (~60 s), stop-file latency improved
  250 ms -> <=10 ms.
- Client response pickup polls every 10 ms (was 100 ms), cutting up to
  100 ms of per-request pickup latency.

Measured result: ~0.2 s/invocation off the warm daemon lane (1.47 -> 1.27 s
median), idle daemon now performs zero subprocess work in steady state
(strace pin: 4 execves per 3 s window = only the two daemon-start execves
plus one drain; pre-fix 26). Pinned by
`test/05_perf/test_runner/light_daemon_wakeup_no_idle_shell_spec.spl`.

Still open (dominant remaining term): the per-request worker
`simple run test_runner_new/test_runner_single.spl ...` re-compiles the
full runner module graph in a fresh child on EVERY request (amortization
factor 1.0, as daemon_backlog.spl already documents). Serving in-process is
the only way to remove it, but the response body is built from the worker's
captured stdout and there is no in-process stdout-capture facility in the
stdlib, so that change needs runtime support or a structured (non-printed)
verdict transport. The lane is still ~0.58 s slower than direct per
invocation because of it.

## Addendum 2026-11-11 (lane ne13) — still LIVE; wakeup fix confirmed in source

**Source verification (tip c8b6d0ebe90e):** the 2026-11-05 wakeup protocol is
in the tree and unchanged — `light_daemon.spl:278-324` idle loop stat()s
`LIGHT_WAKE` in-process every 10 ms (was: `dir_list()` shell-out every 250 ms),
with the 500 ms/5 s fallback sweep and stop-file check; `test_runner_client.spl`
`run_one_via_daemon` bumps the wakeup sequence after the request rename. So
the polling half of this doc's diagnosis is fixed as recorded; the 1.47 -> 1.27 s
median improvement and the still-open ~0.58 s gap stand as the current truth.

**Verification limits of this lane (Windows):** the pinned perf spec
`test/05_perf/test_runner/light_daemon_wakeup_no_idle_shell_spec.spl` fails
2/2 on this host with instrumentation sentinels (`execve count = -1, daemon
ends = -1`) because the light daemon is bypassed on non-linux — exactly the
constraint this doc already records ("must be authored and measured on
linux"). No new wall-clock evidence is possible from this lane; the aarch64
linux measurements in the 2026-11-05 update remain the latest honest numbers.

**Why not fixed in this lane:** the remaining term is the per-request
re-compile (amortization 1.0). The documented fixes are (a) in-process serving,
which needs runtime support for stdout capture or a structured verdict
transport — a runtime/stdlib change with a bootstrap bar, not P3 scope; or
(b) further measurement on an unloaded linux host to separate protocol cost
from contention. Routed to the test-runner/runtime owner.
