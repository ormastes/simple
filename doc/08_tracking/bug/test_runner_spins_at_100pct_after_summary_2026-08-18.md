# `bin/simple test` keeps one thread at 100% CPU after printing its final summary

- **Filed:** 2026-08-18
- **Status:** OPEN — characterised, not fixed. Root cause of the spin NOT located.
- **Severity:** high (host starvation; a spinner also holds a `test-slot.shs` slot)

## Title discipline

The title states only what was measured: a `simple test` process that has already
printed `Results: ... / Some tests failed.` keeps burning a full core. It does
**not** claim to know why. Everything below is split into MEASURED and INFERRED.

## MEASURED — live specimens, 2026-08-18 03:40–03:44 UTC

Four `bin/simple test` processes were live, each ~99–100% CPU, RSS 3.07–3.17 GB:

| pid | argv | elapsed | RSS | last stdout write |
|---|---|---|---|---|
| 3629615 | `bin/simple test test/01_unit/test_runner` | 1158s | 3.12 GB | 03:26:47 |
| 3614825 | `bin/simple test test/fixtures/_accept_run --unstable` | 1209s | 3.17 GB | 03:27:50 |
| 3676172 | `./bin/simple test test/fixtures/_accept_run --unstable` | 1011s | 3.07 GB | 03:29:32 |
| 3860062 | `bin/simple test test/fixtures/unstable_mode --only-skipped --no-unstable --fail-fast` | 508s | 3.10 GB | — |

(All four belong to another session's scratchpad, `.../f157783d-…/scratchpad/*.log`.)

1. **Results were fully DELIVERED, not merely started.** Each log ends with the
   complete block: per-file `SPEC FILE VERDICT:` lines, the `=====` banner,
   `Results: N total, ...`, `Time: ...`, `Some tests failed.` The last byte was
   written 10–14 minutes before the observation and the file mtime never
   advanced afterwards. So the spin is strictly AFTER the summary is emitted and
   flushed. Whether the *result artifacts* (`doc/08_tracking/test/test_db.sdn`
   etc.) were also written was NOT checked — see UNKNOWNS.
2. **The spin is in the runner PARENT, not an unreaped child.** For all four:
   `Threads: 5`, and exactly ONE thread is in state `R` — `comm=simple-main`,
   the interpreter's main worker. The process leader itself is `S` in
   `futex_wait_queue` (it is joining that thread). `ps --ppid` shows **no live
   children** for three of them; 3614825 has one `[sh] <defunct>` zombie (an
   unreaped `process_run_bounded` helper — a real but *separate*, minor defect).
   So the parent/child question is discriminated: **parent**.
3. **The spin is pure userspace, no syscalls.** Over a 10.0s wall window the hot
   thread gained `utime` +1002 ticks (10.02s) and `stime` +0 for every specimen.
   A busy compute/poll loop, not I/O or futex churn.
4. **RSS is the ordinary ~3.1 GB `simple test` footprint**, not a growing
   balloon — it did not move across the observation window. The 14 GB reclaimed
   by killing four such processes earlier is simply 4 × ~3.1 GB retained for the
   duration of the spin, not runaway growth.
5. Attach-based profiling is unavailable on this host (`ptrace_scope=1`,
   `perf_event_paranoid=4`), so no stack for the hot thread was obtainable.

## MEASURED — why nothing killed them: the `kill-simple-monitor` CPU guard is dead

The brief's premise "the unit is NOT logging its kills" is **false**.
`/tmp/kill_simple_monitor.log` is 1.6 MB with **5485 KILL lines**, of which
**5422 are `cpu=` kills**. But:

- **The last `cpu=` kill is `2026-08-17T06:30:25`.** Every kill after that
  (13:00 through the last entry 22:58) is an `rss=` kill. Nothing has been
  logged at all since 22:58, while the four spinners above ran unmolested.
- `/tmp/.kill_monitor_cpu_1000/` — the per-pid prior-sample state directory
  introduced by the 2026-08-17 `instant_cpu_pct` rewrite — is **empty**, with
  directory mtime `Aug 17 06:36`, i.e. the moment the rewrite went in. No sample
  file has persisted since.
- `instant_cpu_pct()` returns EMPTY when there is no prior sample, and the
  caller correctly treats empty as "no evidence" and skips the kill. With no
  state file ever surviving, `cpu_int` is always empty, `spin_streak` never
  reaches `SPIN_SAMPLES=3`, and **the CPU guard can never fire**. Only the RSS
  guard (single-sample, no history) still works — exactly matching the log.
- Direct probe (isolated lock/state dirs, thresholds raised so it could kill
  nothing): under this host's load a single poll pass over `ps -eo …args` did
  **not complete within 45s** with `KILL_SIMPLE_INTERVAL=5`. The `sh -x` trace
  covered only ~2500 lines and reached just the first matching pid. Multi-KB
  argv lines (an agent prompt of several KB is one `case` operand) make each
  iteration expensive.
- Separately, `systemctl --user show` reports `NRestarts=3633`, a fresh
  `ExecMainPID` roughly every 15s, and `ExecMainCode=0/1 ExecMainStatus=0` —
  clean exits, not crashes. Consistent with `acquire_lock` losers exiting 0 and
  `Restart=always`/`RestartSec=5` respawning, but the surviving instance's short
  life was NOT explained.

Script: `/home/ormastes/dev/pub/simple/scripts/resource/kill_simple_monitor.shs`
(note: **outside** this worktree).

## INFERRED (explicitly not proven)

- That the empty state dir is caused by the poll pass never completing (so the
  script is still inside its first `ps | while read` when it is replaced) is the
  most economical explanation, but the write itself was never observed to fail:
  `printf > /tmp/.kill_monitor_cpu_1000/<pid>` succeeds by hand.
- That the CPU-guard regression was introduced by the 2026-08-17 rewrite is
  supported by the timestamps coinciding to within six minutes; it is not a
  bisect.
- No causal claim is made about WHAT the runner spins on. Candidates not
  discriminated: post-summary bookkeeping (test_db/feature-doc regeneration), a
  poll loop awaiting an already-dead child, or interpreter shutdown/teardown.

## Second harm

`scripts/resource/test-slot.shs` caps concurrency at 12 via `flock`. A spinner
holds its slot for the whole spin, so ~14 minutes of dead weight per specimen
blocks a real lane even though the run is logically finished. Four concurrent
spinners is a third of the machine's entire test concurrency budget.

## Third harm (traceability)

Because the CPU guard has been silently dead since 2026-08-17T06:30, an rc=143
in this window is **not** attributable to the monitor either — the monitor is
not killing anything on CPU. Per `.claude/rules/testing.md`, rc 143/137/144 with
no result line stays UNVERIFIED regardless.

## UNKNOWNS to close next

1. Are the result artifacts (`test_db.sdn`, `test_result.md`, feature docs)
   written before or after the spin begins? Compare their mtimes against the
   stdout log mtime on a fresh specimen.
2. What is the hot thread executing? Needs either `ptrace_scope=0` (root) or an
   in-runner instrumentation build.
3. Why does the surviving `kill_simple_monitor` instance exit every ~10–15s?

## Actions taken / not taken

- **Nothing was killed.** At the time of observation `free -g` showed 86 GB
  available and a bootstrap was the priority workload; the four spinners belong
  to a live sibling session that may still be waiting on their exit status.
  State recorded above instead.
- No code change. The monitor lives in a different tree and the runner's spin
  site is unlocated; neither fix is "small and obvious".
