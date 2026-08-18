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

---

## 2026-08-18 — CPU guard root-caused and FIXED; spin site narrowed (not proven)

### 1. Why the CPU guard could not fire — exact, one line

`scripts/resource/kill_simple_monitor.shs` runs under `set -e`. In
`instant_cpu_pct`:

```sh
_prev=$(cat "$_f" 2>/dev/null)          # <-- no `|| true`
printf '%s %s %s\n' ... > "$_f"         # <-- never reached on first sighting
```

On the **first** sighting of any pid the state file does not exist, `cat` exits
1, the assignment inherits status 1, and `set -e` **terminates the whole
monitor** — on the line *before* the `printf` that would have created the state
file. So: no state file is ever written, no pid ever has a prior sample,
`instant_cpu_pct` always returns empty, the caller correctly skips,
`spin_streak` never reaches 3, and the CPU guard is **structurally incapable of
firing**. `/tmp/.kill_monitor_cpu_1000/` being empty with a `06:36` mtime is not
a symptom of a slow poll — it is the direct consequence.

The daemon looked healthy: `systemctl --user status` reported `active
(running)` while systemd respawned the corpse every ~15 s (10 s sleep +
`RestartSec=5`). **Restart counter was 3735** when found, consistent with the
last `cpu=` kill at 2026-08-17T06:30 and the rewrite's own 06:36 timestamp.

Two more `set -e` landmines of the same class were found and fixed:
`_n=$(cat "$_f")` in `spin_streak`, `_holder=$(cat "$LOCKDIR/pid")` in
`acquire_lock`, and the `tr|sed|head` in `cpu_budget_secs`.

Separately, `cleanup()` ended in `exit 0`, so a fatal startup failure was
reported to systemd as a clean stop. It now preserves `$?`.

### 2. The "one poll pass takes >45 s" lead is REFUTED

Measured with the new `SLOWPOLL`/`HEARTBEAT` instrumentation, interval 5,
254 uid-1000 processes on a loaded host:
`last_poll_secs=0`, `0`, `1`, `0` over 13 polls. The poll pass is sub-second.
The multi-KB argv `case` operands are **not** a cost problem. The previous
lane's 45 s observation is better explained by the `set -e` death (the pass
never completed) plus `kill_hard`'s `sleep 1` per victim when thresholds were
lowered globally.

### 3. Visibility (a dead guard must be visible)

- **Startup assertion** `selftest_state_dir()`: writes and reads back a probe
  file in the CPU state dir. On failure it logs `FATAL`, prints to stderr, and
  **exits non-zero** rather than degrading silently to RSS-only.
- **`START` line** recording pid, interval, thresholds and state dir.
- **`HEARTBEAT` line** every `KILL_SIMPLE_HEARTBEAT_SECS` (default 300) with
  `polls=`, `last_poll_secs=`, `samples=`. A heartbeat that keeps reporting
  `samples=0` while simple processes run means the CPU guard is dead again;
  absence of heartbeats means the daemon is.
- **`SLOWPOLL` line** when a pass exceeds the interval — recorded, not hidden
  by widening the interval.

### 4. New: `KILL_SIMPLE_ONLY_PIDS` (test-safety allowlist)

Unset in production (no behaviour change). When set, `kill_hard` refuses any
pid outside the list. This exists because the only previous way to exercise a
guard was to lower a threshold **globally** — and doing so during this
investigation killed five other sessions' processes (recorded below).

### 5. Spin site — narrowed, NOT proven

The bug record's `Threads: 5`, leader `S` in `futex_wait_queue` joining one `R`
thread named `simple-main`, was read as evidence of a stuck worker. It is not:
`src/compiler_rust/driver/src/main.rs:1096-1112` re-spawns `real_main()` on a
thread *named* `simple-main` with a 64 MB stack and immediately `join()`s it.
That topology is the **normal** shape of every run. The spinning thread IS the
program's main logic, and there is no test-runner worker pool (no
`thread_spawn`/actor spawn anywhere under
`src/lib/nogc_sync_mut/test_runner/` or `src/app/test_runner_new/`).
**The "worker spinning on an unsignalled flag" hypothesis is refuted.**

The live entry is `src/app/test_runner_new/test_runner_main.spl` (note:
`src/app/test/test_runner_main.spl` does not exist). Tail after the summary
(`print_summary` at :1117-1118, emitted by `test_runner_output.spl:210`):

| step | site |
|---|---|
| coverage collect/report (only with `--coverage`) | :1120-1133 |
| **`update_test_database(...)`** | :1136-1137 |
| unverified-file naming loop | :1142-1150 |
| spl_doctest / sdoctest modes | :1160-1179 |
| `generate_test_result_md` + atomic write | :1182-1187 |
| returns `exit_code` — **no explicit `exit()`**, falls off main | :1200 |

Prime suspect, consistent with utime-climbing / stime-0 / no-syscalls:
`src/lib/nogc_sync_mut/test_runner/test_runner_helpers.spl:238-252` —
per-file `db.update_test_result`, then `db.cleanup_stale_runs(48)` and
`db.save()` re-serialising `doc/08_tracking/test/test_db.sdn` (147 KB) and
`test_db_runs.sdn` (192 KB) in the tree-walk interpreter. Also
`update_features_from_tests` (:261-285) contains a genuinely **quadratic**
nested loop (`for feature in all_features` x `for file_result in
result.files`), though no call site for it was found on this path.

This reframes the defect: most likely **not** a spin-wait but an unbounded /
superlinear CPU-bound teardown that never terminates in practical time. That
distinction matters — it is not fixable by signalling a flag.

Spin constructs checked and cleared: `resource_monitor.rs:165-192` (condvar
`wait_for`), `interpreter_extern/system.rs:118-155` (10 ms sleep poll),
`examples_safety.rs`, `native_all/lib.rs:1489`, `resource_governor.spl:77`.

**NOT verified:** which of the two candidates consumes the time. Attach
profiling is blocked here (`ptrace_scope=1`, `perf_event_paranoid=4`), and the
instrumented run needed to settle it was not performed — the host was carrying
a priority bootstrap and a runner run costs ~5+ min of a contended box.
`scripts/check/check-test-runner-exits-after-summary.shs` is written to
measure the post-summary tail directly, and **has not been run**.

### 6. Collateral damage, disclosed

Before `KILL_SIMPLE_ONLY_PIDS` existed, a probe run with
`KILL_SIMPLE_MEM_MB=0` (a global threshold) killed five processes belonging to
other sessions, at 2026-08-18T04:12:

- `417410` `simple run native_build_worker.spl ... engine_differential/nested_list_of_lists.spl`
- `421162` `timeout 1200 bin/simple test test/01_unit/compiler/interp/execir_slice_spec.spl`
- `421165` `bin/simple test test/01_unit/compiler/interp/execir_slice_spec.spl`
- `423979` `bin/simple test test/01_unit/startup/cli_extension_config_registry_spec.spl`
- `424890` `simple run native_build_worker.spl ... extern_unimplemented_weak_stub/negative`

The running bootstrap (pids 487745/487751/488825, worktree
`simple-stage4-clean`) was **not** affected and was verified alive afterwards.
A later `pkill -f kill_simple_monitor` also stopped the systemd-managed monitor
instance; systemd restarts it automatically.

### 7. Tests

`scripts/check/check-kill-monitor-cpu-guard.shs` — 6 cases, all fixture-scoped
via `KILL_SIMPLE_ONLY_PIDS`, isolated lock/state/log dirs:

```
cpu_guard_fires              expect=killed got=killed monitor_alive=yes samples=16
survives_and_samples         alive=yes samples=14 heartbeats=4
rss_guard_still_fires        expect=killed got=killed monitor_alive=yes samples=0
brief_spin_not_killed        expect=alive  got=alive  monitor_alive=yes samples=18
idle_not_killed              expect=alive  got=alive  monitor_alive=yes samples=21
startup_selftest_is_loud     exit=1 loud=1
PASS — 6 case(s) checked, CPU guard fires, RSS guard intact, healthy work spared
```

**Negative control** (revert the single `|| true` on `_prev`, keep the
allowlist so the control stays safe):

```
REVERTED: victim ALIVE (guard did not fire) samples=0
FIXED:    victim KILLED (guard fired)       samples=10
```

The reverted monitor exits 1 on its first poll, exactly as the daemon had been
doing 3735 times.

### 8. Activation is DEFERRED — action required

The script is fixed but the running daemon has **not** been restarted, and no
systemd unit was modified. Restarting it would bring a live CPU guard back for
the first time in a day **while a priority bootstrap is running**; the guard
exempts `native_build_main.spl`/`native_build_worker.spl` by argv but not every
CPU-bound bootstrap child. Restart once the bootstrap completes:

```sh
systemctl --user restart kill-simple-monitor
grep -E 'START|HEARTBEAT|FATAL' /tmp/kill_simple_monitor.log | tail
```

Expect a `START ... selftest=ok` line, then `HEARTBEAT ... samples=<n>` with
`n > 0`. `samples=0` or no heartbeat means the guard is dead again.
