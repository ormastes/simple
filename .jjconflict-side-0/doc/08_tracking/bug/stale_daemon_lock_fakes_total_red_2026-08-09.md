# Stale light-daemon lock fabricates a total-RED baseline

- **Status:** FIXED 2026-08-09
- **Severity:** high (fabricates a whole-corpus failure; no verdict lines)
- **Area:** `src/app/test_runner_new/test_runner_client.spl`, `src/app/test_daemon/main.spl`

## Symptom

With a stale `.build/test_daemon_light/daemon.lock`, **every** spec exits 1 with

```
ERROR: test daemon timed out: <path>
```

and no verdict line. A sweep reads this as "the entire corpus just went red",
which is both false and unactionable — nothing in the output points at the lock.

## Root cause

Liveness was `kill -0 <pid>` and nothing else. A lock left by a crashed daemon
whose PID has since been **reused** by an unrelated process passes `kill -0`, so
`ensure_daemon()` concluded a daemon was alive, never respawned one, and every
request then waited out its full budget with nobody serving the queue.

## Fix

Liveness now additionally requires `/proc/<pid>/cmdline` to name
`light_daemon`. Deliberately conservative in both directions:

- A **D-state** (uninterruptible) daemon still matches its own cmdline, so it is
  reported alive and never disturbed — it may be making progress.
- Where `/proc` is unavailable (non-Linux), the probe is skipped and the
  `kill -0` answer stands, exactly as before.

Only the lock **file** is ever removed, and only for a PID that is provably not
the daemon. No process is ever signalled — in particular there is no `pkill`.
Detection is announced before the self-heal (naming the lock path and the manual
remedy `rm -rf .build/test_daemon_light`) so a recurring stale lock stays
visible rather than being silently papered over. The client's no-response
timeout also now prints the lock path and the remedy.

## Proof (real trigger, not a mock)

Isolated lane (`$SCRATCH/lane/.build/test_daemon_light/`), lock written with the
PID of a live, non-daemon process (`nohup sleep 1800`, pid 4175977, cmdline
`sleep 1800`). Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 29577536
bytes, mtime 2026-08-09 04:50:31.

BEFORE (`git show HEAD:src/app/test_daemon/main.spl`):

```
$ simple run src/app/test_daemon/main.spl status
Test daemon: running (pid: 4175977)
lock after: [4175977]
```

A `sleep` is reported as a live test daemon and the lock is retained — the exact
state that starves every subsequent request.

AFTER:

```
$ simple run src/app/test_daemon/main.spl status
Test daemon: not running
lock after: []
```

Stale lock detected and removed; decoy pid 4175977 verified still alive
afterwards (never signalled).

A matching client-side control confirmed the silence being fixed: with the HEAD
client and the same stale lock, the run hung to a 300 s external kill,
exit 124, `grep -c 'SPEC FILE VERDICT' = 0`.

## See also

- `doc/07_guide/infra/testing.md` § Runner Operational Caveats, item F6
- `killed_spec_emits_no_verdict_line_2026-08-09.md`
