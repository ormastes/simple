# `simple test <dir>` prints its complete summary and then never exits (post-run DB/report phase)

- **Date:** 2026-08-18
- **Lane:** NONEXIT
- **Binary:** `bin/simple` — the **Rust seed** (it says so on stderr). Attribute to the seed.
- **Status:** OPEN — reproduced twice, localized to the post-summary phase by ablation. Not fixed
  (the fix is not small and not certain; see "Why not fixed here").
- **Severity:** the run's EXIT CODE is unobservable, and a CI slot is burned forever.

## Symptom

```
bin/simple test test/fixtures/_accept_run --unstable
...
Results: 4 total, 2 passed, 2 failed, 1 skipped, 1 crashed, 1 timed out (unverified)
=========================================
Some tests failed.
```

The summary is COMPLETE and correct. The process then keeps running at ~100% CPU on one
thread and does not exit.

## Does it exit on its own? NO.

| run | flags | wall | outer `timeout` | runner's OWN rc |
|---|---|---|---|---|
| A | `--unstable` | killed at **1801s** by `timeout 1800` | 1800s | **never produced** (wrapper rc 124) |
| B | `--unstable --no-db` | **265s, exited on its own** | 1800s (not reached) | **124** |

Summary line printed at t+250s in run A. **1538s elapsed from summary line to the kill with no
exit.** rc was captured on the line AFTER the command, never through a pipe; run A's `124` is the
*wrapper's*, not the runner's. Run B's `124` is the *runner's own* exit code (only 265s of a
1800s budget had elapsed, so `timeout` cannot have produced it) — i.e. with `--no-db` the runner
terminates and reports.

Reproducer (exactly what was run):

```sh
timeout 1800 bin/simple test test/fixtures/_accept_run --unstable   # hangs
timeout 1800 bin/simple test test/fixtures/_accept_run --unstable --no-db   # exits, rc=124
```

## What it waits on — /proc evidence

Process 3614825 (run A), sampled repeatedly after the summary:

```
Threads: 5
3614825 simple           futex_wait_queue  S   utime 0
3614826 simple-main      (wchan 0)         R   utime 102175 -> 102674 over 5s  == 99.8% CPU
3614827 tracing-appende  futex_wait_queue  S
3614838 ctrl-c           futex_wait_queue  S
3614839 simple-main      futex_wait_queue  S   utime 16
VmRSS: 3167240 kB -> 3167264 kB over 40s   (flat: a compute loop, not runaway allocation)
/proc/3614825/fd:  0 -> /dev/null, 1,2 -> out.log, 3 -> .simple/logs/simple.log.2026-08-18
children: one `[sh] <defunct>` zombie, nothing else
```

Reading:

- The PID's **main thread is blocked in `handler.join()`** at
  `src/compiler_rust/driver/src/main.rs:1108` — `main()` re-enters `real_main()` on a named
  `simple-main` thread with a 64 MB stack and joins it. That join is the `futex_wait_queue`.
- Thread `simple-main` (3614826) — the one running `real_main()` — is **state R, burning 99.8%
  CPU** with a flat RSS and no syscall activity. The runner is not blocked on anything; it is
  *computing*.
- **No sockets in `/proc/<pid>/fd`.** Hypothesis (c) "session-daemon connection left open" is
  REFUTED for the hang (the directory run does go through the daemon, but no socket fd survives
  into this phase).
- **No live children.** Hypothesis (b) "the timeout fixture's child outlives the lane" is
  REFUTED — the timed-out child is gone. Hypothesis (a) "SIGKILLed crash child never reaped" is
  REFUTED *as the cause*: there IS one un-reaped `[sh]` zombie, but no thread is in `wait`, so
  nothing blocks on it. (The zombie is a separate, cosmetic leak, from the `kill -TERM/-KILL`
  helper `Command`s in `wait_with_timeout`, `driver/src/cli/test_runner/execution.rs:1713-1719`,
  whose `Child`ren are dropped without reaping.)

## Where the time goes (file-mtime timeline, run A)

Relative to the summary line at T0:

| T0+ | evidence | phase |
|---|---|---|
| +58s | `doc/08_tracking/test/test_db.sdn` mtime | `update_test_database(...)` finished, incl. `db.save()` |
| +845s | `doc/08_tracking/test/test_result.md` mtime | `generate_test_result_md(database)` finished (~780s for that one call) |
| +845s .. +1538s | 99.8% CPU, flat RSS, no I/O | **unidentified** — still spinning when killed |

Code path, all of it interpreted by the seed
(`src/app/test_runner_new/test_runner_main.spl`):

- `1118: print_summary(spec_result, options.format)` — the last thing the user sees
- `1135: if result_files.len() > 0 and not options.list and not options.no_db: db = update_test_database(...)`
- `1181-1186: match db: Ok(database): ... generate_test_result_md(database); file_atomic_write("doc/08_tracking/test/test_result.md", ...)`
- `1200: exit_code`

Both post-summary steps are gated on `not options.no_db`, which is exactly the ablation that
makes the process exit — so the hang lives in this block or in what it leaves behind.

`generate_test_result_md` is `src/lib/nogc_sync_mut/test_runner/doc_generator.spl:25`; its query
API is `RunnerTestDb` (`test_db_compat.spl:99-120` -> `test_db_core.spl`). The DB is small
(`doc/08_tracking/test/test_db.sdn`, 4372 lines, ~2000 interned spec paths) — 780s to emit a
report from it is itself a defect, independent of the non-exit.

The residual +693s AFTER the report was written is the part that is genuinely unexplained. Flat
RSS at 3.1 GB with 100% CPU and zero I/O is consistent with teardown/drop of the large object
graph the DB path builds (which `--no-db` never builds), but that is a HYPOTHESIS, not
established. Attach-based profiling could settle it and is blocked on this host
(`ptrace_scope=1`, `perf_event_paranoid=4`) — same constraint recorded in
`doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`.

## Not a one-off

A second, unrelated lane's process was found in the identical state during this investigation:
PID 2137862, `bin/simple test test/fixtures/unstable_mode --only-skipped --unstable`, **8439s
(2h20m) elapsed**, main thread in `futex_wait_queue`, its `simple-main` thread state R with
824663 ticks of user time and climbing ~100 ticks/s, no children, no sockets. Same shape.

## Why not fixed here

Three candidate faults are in play (the ~780s report generation, the unexplained ~693s residual,
and the zombie leak) and only the third is small. Deleting or fast-pathing the post-run DB/report
work would change what `simple test` writes to tracked, auto-generated artifacts, which is well
outside a hang fix. Nothing was changed; this is filed with the reproducer and evidence instead.

## Notes for whoever picks this up

- `--no-db` is a usable workaround **only** when the run does not need `test_db.sdn` /
  `test_result.md` refreshed. It does not make the exit code correct, it just makes one exist.
- A directory run cannot use `--no-session-daemon` ("expected .spl test file"), so daemon
  involvement cannot be ablated the same way — but the fd evidence already rules the daemon out.
- rc 143/144 is unverified, never a failure, on this host (earlyoom). Neither run here hit that:
  run A's 124 is `timeout`'s SIGTERM at exactly its 1800s deadline, run B exited by itself.
