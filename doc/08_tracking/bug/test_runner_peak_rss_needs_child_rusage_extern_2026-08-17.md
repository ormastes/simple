# Supervised test runner cannot report peak RSS — no child-rusage extern exists

- **Filed:** 2026-08-17 (lane RSS)
- **Status:** OPEN — NOT implemented. Blocked on a new runtime extern + seed redeploy.
- **Requirement:** `doc/02_requirements/infra/supervised_test_runner.md` R6
  ("path, outcome, signal/exit code, wall time, peak RSS").
- **Related:** `doc/08_tracking/bug/supervised_builder_unwired_and_no_peak_rss_2026-08-17.md`
  (the BUILD-side half of the same hole).

## Gap confirmed independently (not taken from the prior audit)

`/usr/bin/grep -rniE 'rss|maxrss|VmHWM|getrusage'` over
`src/lib/nogc_sync_mut/test_runner/` and `src/app/test_runner_new/` returns
exactly **one** hit, and it is unrelated (`test_runner_types.spl:155`, a comment
on the `batch_size` "hidden parent-RSS batch transport" option). No peak-RSS
value is captured, stored, or printed anywhere on the test side.

## Where a unit's outcome record is built

`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` — the natural home,
directly alongside the existing wall-time/exit-code capture:

- `:171` `val start = time_now_unix_micros()` — start of the timed phase
- `:176` `process_run_with_limits_bounded(...) -> ProcessResult` (limits path)
- `:199` `process_run_bounded(...) -> (stdout, stderr, exit_code)` (default path)
- `:201-203` `exit_code = code` / `val end = ...` / `val duration_ms = (end - start) / 1000`
- `:240-247` the `TestFileResult` is constructed here

The same shape repeats for the SMF path (`:287-312`), the native path
(`:805-836`) and safe mode (`:866-875`).

## Why neither obvious Linux source works today

1. **`/proc/<pid>/status` `VmHWM`** — unusable, and not merely awkward. The
   child's PID is **never exposed to Simple**. `process_run_bounded` /
   `process_run_with_limits_bounded` are synchronous: they spawn, wait, and reap
   entirely inside the runtime, returning only text/exit code. `/proc/<pid>/*`
   vanishes at reap, so any read a Simple caller could issue is necessarily
   after the directory is gone. This file's own header (`:6-7`) already records
   the constraint: *"Current implementation uses synchronous execution which
   doesn't expose PIDs."* A pre-reap read would have to happen inside the
   runtime's wait loop — i.e. a runtime change, which is the same conclusion.

2. **`getrusage(RUSAGE_CHILDREN).ru_maxrss`** — survives the reap (the kernel
   folds a child's rusage into the parent at `wait()`), so it dodges problem 1,
   but from Simple it is **not per-unit**: it is the running maximum over *all*
   children this process has ever reaped, and is monotone non-decreasing. A
   before/after delta therefore yields only a lower bound — it reports a number
   when a unit sets a new high-water mark, and silently reports "no change" for
   every unit below the session maximum. For a runner whose whole purpose here
   is distinguishing "this spec is heavy" from "the host was under pressure",
   an attribute that goes blank precisely on the *second* heavy spec is worse
   than useless. Correct per-unit attribution needs the rusage captured at the
   individual `wait4()`, i.e. inside the runtime.

3. **What the runtime already has, and why it does not help.**
   `rt_process_hwm_kib` exists (`src/runtime/runtime.c:1965`,
   `src/runtime/runtime_legacy_core.c:563`) but reads `/proc/self/status`
   `VmHWM:` — the *runner's own* peak, not the child's. Surfacing it per unit
   would attribute the parent's memory to whichever spec happened to run when
   the parent grew. Not a substitute.
   (Aside, unrelated defect noticed in passing:
   `src/lib/nogc_sync_mut/platform_measurement_observer.spl:13` imports
   `process_peak_rss_kb` from `std.nogc_sync_mut.io.sysinfo_ops`, and that name
   does not appear in `sysinfo_ops.spl`. Not this lane's file; noted only so it
   is not mistaken for an existing peak-RSS API.)

## The exact change needed (one small step)

**A. Runtime extern (Rust seed + C runtime) — requires a seed redeploy.**
Capture the child's rusage at its own `wait4()` and return it:

```c
/* src/runtime/... alongside the existing bounded-run entry points */
/* wait4(pid, &status, 0, &ru) instead of waitpid(pid, &status, 0); */
/* peak_rss_kib = ru.ru_maxrss   (Linux reports KiB; macOS reports BYTES —
   divide by 1024 there, else the number is 1024x wrong) */
int64_t rt_process_last_child_peak_rss_kib(void);
```

Minimal-blast-radius shape: a thread-local `int64_t` set by the bounded-run
implementations at reap, read by a new extern. This avoids changing the ABI of
`rt_process_run_bounded` / the limits variant, so no existing caller moves.
Fallback contract: return `-1` where unsupported (not `0` — `0` is a plausible
real value and would be indistinguishable from "unmeasured", which is exactly
the failure mode the build-side bug above already documents as "always-0").

**B. Two pure-Simple files, both outside lane RSS's ownership.**
- `src/lib/nogc_sync_mut/io/process_ops.spl` — add `peak_rss_kib: i64` to
  `struct ProcessResult` (`:44-49`) and return it from
  `process_run_with_limits_bounded` (`:462`); `process_run_bounded` (`:76`)
  returns a bare 3-tuple, so it needs either a 4-tuple or a sibling entry point.
- `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl` — add
  `peak_rss_kib: i64` to `struct TestFileResult`, plus rendering in
  `test_runner_output.spl`.

**C. Then** `test_runner_execute.spl` (this lane's file) is a ~4-line change at
each of the four capture sites.

## Why this lane stopped here rather than half-landing it

Every path to a *reportable* number crosses at least one file this lane does not
own and, for a correct per-unit number, a runtime extern plus a seed rebuild —
which the lane is explicitly forbidden from doing. A `/usr/bin/time -f %M`
wrapper around the child was considered as an SFFI-free dodge: it would produce
a real per-child number without any runtime change, but it still has nowhere to
be stored (`TestFileResult` has no field) and would inject text into the stderr
stream that `test_executor_parsing.spl` parses for spec outcomes. Landing that
would trade a missing metric for a corrupted verdict. Rejected.

**R6 therefore remains NOT SATISFIED, and must not be marked otherwise until a
real number is observed for a real spec.**

## Resume command (for whoever redeploys the seed next)

```bash
# 1. add the extern (A above) in src/runtime/ + src/compiler_rust/runtime/
# 2. bin/simple build bootstrap        # required: runtime extern => seed rebuild
# 3. thread peak_rss_kib through B, then C
# 4. prove by ablation, not by inspection:
bin/simple test test/01_unit/<some>/<real>_spec.spl   # expect a nonzero peak RSS on the unit line
#    then revert the execute.spl hunk and confirm the number disappears; restore.
# 5. flip the R6 peak-RSS row in doc/02_requirements/infra/supervised_test_runner.md
```

Note when measuring: `rc=143`/`144` is UNVERIFIED, never a failure — earlyoom is
actively SIGTERMing multi-GB processes on this host. Re-run, do not record.
