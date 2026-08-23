# native-build wrapper reports a healthy worker as "exited abnormally (code -1)" and kills its session

- **Date:** 2026-08-23
- **Status:** FIXED
- **Severity:** high — each occurrence costs a full stage1 attempt (~70 min)
- **Gate:** `sh scripts/check/check-process-wait-eintr-retry.shs`

## Symptom

```
error: native-build worker wrapper exited abnormally (signal or wait failure, code -1)
       before producing a binary; its process group has been terminated.
[attempt 1] rc=255 wall=4107s
```

Observed in stage1 run18 (rc=255 at `hir 181/688`, 4107s), run17 (rc=255, 3811s),
and two `--entry-closure` probe runs from an unrelated lane — same signature,
different trees and entries. Already excluded by measurement: OOM killer
(24 GB free, no `dmesg` kill), disk-full (70 G free), the resource monitor
(`SIMPLE_TIMEOUT_SECONDS=0` exempts these runs), and the one self-reported
over-broad `pkill` (timestamps prove it did not touch run18).

## Mechanism

Three defects compose.

1. **`rt_process_wait()` never retried an interrupted wait.** In
   `src/runtime/runtime_process.c` the loop was
   `pid_t r = waitpid(pid, &status, WNOHANG); if (r < 0) return -1;` — an
   `EINTR` return, which does **not** touch the child, was reported as a failed
   wait. Any signal delivered to the *wrapper* over a multi-thousand-second
   build (SIGALRM/SIGCHLD/SIGWINCH…) could produce it. The Rust runtime's
   `rt_process_wait` (`env_process.rs`) had the same hole via
   `try_wait()`/`wait()` returning `ErrorKind::Interrupted`, plus a poisoned
   `SPAWNED_CHILDREN` mutex being turned into a permanent `-1`.
2. **A signal death and a failed wait were the same value.** Both runtimes
   collapsed every non-`WIFEXITED` status onto `-1`
   (`status.code().unwrap_or(-1)`), so the caller could never say which of the
   two had happened — which is exactly why the error text has to hedge with
   "(signal or wait failure)".
3. **The `-1` then triggered a session kill.** In
   `src/lib/nogc_sync_mut/io/process_ops.spl`, `process_run_timeout_live`'s poll
   loop exits as soon as `_process_wait_raw` returns anything other than `-2`.
   A spurious `-1` therefore left the loop with a *live, healthy* worker,
   `_process_is_running_raw(pid)` said false (the Rust registry had already
   dropped the child), so `timed_out` was false, and the unconditional
   `if exit_code != 0: _process_kill_group(pgid_file)` `pkill -KILL -s`'d the
   whole session. A recoverable hiccup became a lost hour.

So the class is **(b) a wait/reaping defect where a healthy child's status is
lost**, with (a) misreporting layered on top. Genuine external signalling
explains at most some individual instances, not the class.

## Evidence

`src/runtime/test/rt_process_wait_eintr_selfcheck.c` executes the real
`rt_process_wait` against a real child while an `ITIMER_REAL` fires a handler
installed **without** `SA_RESTART`. Pre-fix:

```
  ok:   the wait really was interrupted at least once (got 1)
  FAIL: interrupted blocking wait retries and returns the child's exit code: got -1, want 7
  FAIL: SIGKILLed child reports 128+signo, not the -1 error sentinel: got -1, want 137
```

Post-fix all four checks pass (exit codes 7 and 137 respectively). That `-1` is
byte-for-byte the `code -1` in the production message.

## Fix

- `src/runtime/runtime_process.c`: retry `waitpid` on `EINTR` in both the
  blocking and the `WNOHANG` path; new `rt_process_status_to_code()` reports
  `128 + WTERMSIG` for a signal-terminated child. `-1` now means *only*
  "indeterminate".
- `src/compiler_rust/runtime/src/value/sffi/env_process.rs`: retry on
  `ErrorKind::Interrupted` without dropping the child; recover a poisoned mutex
  instead of failing forever; `exit_status_to_code()` reports `128 + signal`;
  a non-interrupted error keeps the child **tracked** so a later wait and
  `rt_process_is_running` can still see it.
- `src/lib/nogc_sync_mut/io/process_ops.spl`: new `_process_group_alive()`
  (`pkill -0 -s`, the same session id `_process_kill_group` kills). An
  indeterminate `-1` whose session is still alive no longer ends the poll loop,
  and the group is reaped only on a real non-zero exit or a timeout.
- `src/app/cli/native_build_main.spl`: the indeterminate case now says the
  status was lost and that the process group was **left intact**, instead of
  claiming an abnormal exit and a termination that no longer happens.

## Follow-up

The Rust-side half only takes effect after a seed rebuild; the C-runtime and
Simple-side halves are live immediately (stdlib is read as source).
