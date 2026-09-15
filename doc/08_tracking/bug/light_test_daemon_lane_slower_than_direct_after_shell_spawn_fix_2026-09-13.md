# Light test-daemon lane is slower than the direct lane even after removing all `/bin/sh` spawns from `daemon_lock_alive()`

- Status: OPEN (2026-09-13)

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
