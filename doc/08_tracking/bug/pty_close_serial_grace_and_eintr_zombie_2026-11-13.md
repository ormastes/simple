# PTY close: serial per-pane grace on teardown, EINTR drops the child record

- **ID:** pty_close_serial_grace_and_eintr_zombie_2026-11-13
- **Severity:** P3
- **Status:** fixed (work/smux-reap-20261113)
- **Found by:** follow-up to PR #8885 (`2fbfd3498a2`, resolution section of
  `caret_smux_multi_launch_adapter_missing_2026-08-21.md`), which recorded both
  residuals.
- **Area:** PTY provider (`src/compiler_rust/runtime/src/value/pty.rs`,
  `src/compiler_rust/compiler/src/interpreter_extern/pty.rs`), smux teardown
  (`src/os/apps/smux/child_lifecycle.spl` `close_owned_children`), used by the
  caret smux multi-launch adapter's rollback and stop-all.

## Symptoms

1. **Close latency is serial.** `reap_pty_child` waits up to ~1 s for a
   hung-up child before SIGKILL. `smux_kill_session` closes its panes one after
   another, so a team of N children costs up to N s to roll back or stop.
   Measured at base `2fbfd3498a2` with a seed built from it, 4 panes through
   `caret_smux_launch_team` + `caret_smux_stop_all`:

   | children | stop_all |
   |---|---|
   | 4 x `/bin/sh` | 3073 ms |
   | 4 x SIGHUP-ignoring script | 4077 ms |

   The plain-shell row was not expected: interactive shells exit on hangup at
   once. Cause: `openpty` masters (and pending slaves) are not `FD_CLOEXEC`, and
   a spawned child closes only its own master, so pane k's child inherits and
   holds the masters of panes 1..k-1. Closing pane 1's master then hangs up
   nobody, and every close but the last pays the full grace period.
2. **EINTR zombie.** The compiled-lane `pty_process::is_running` dropped the
   `CHILD_TABLE` record on any non-zero `waitpid(WNOHANG)` result, including
   `-1/EINTR`. With the record gone `rt_pty_close` no longer reaps the child, so
   it stays a zombie (and `kill(pid, 0)` keeps reporting it alive). The
   interpreter lane kept the record on EINTR but reported the child as not
   running for that probe, and kept a stale record forever on ECHILD.

## Red (runtime unit tests, `cargo test -p simple-runtime --lib value::pty`)

- `hangup_then_close_of_n_sighup_ignoring_children_costs_one_grace` — 4.06 s
- `close_hangs_up_its_child_while_a_sibling_pane_is_alive` — 1.01 s
- `is_running_keeps_the_child_record_when_the_wait_is_interrupted` — record
  dropped. EINTR is injected through an `is_running_with` wait seam: a real
  `waitpid(WNOHANG)` practically never returns EINTR, so a signal-driven test
  would not be deterministic.

## Resolution 2026-11-13 (work/smux-reap-20261113)

1. **FD_CLOEXEC on the PTY pair** (both lanes' `open`, shared
   `set_pty_fd_cloexec`). The child clears the flag on fds 0-2 after its
   `dup2`s (a slave already at 0-2 would otherwise close on exec). `dup2` onto 0/1/2 clears the flag, so the child's
   own stdio is unaffected; later panes' children no longer inherit earlier
   masters, so closing a master hangs up its own child at once.
2. **`rt_pty_hangup(handle) -> bool`**, Rust runtime + interpreter + C lane
   (`std.sys.pty.hangup`, `sosix_pty_hangup`; windows_native provider answers
   false). Under the child-table lock it sends SIGHUP to the child's session
   group and stamps `PtyChildRecord.hung_up_at`. `rt_pty_close` stays the only
   closer and reaper: `reap_pty_child_record` runs the 1 s grace from the stamp
   (from now when never hung up, i.e. single close unchanged), checks the child
   at least once even after the shared deadline, then SIGKILLs the group and
   reaps. The signal is sent while the record is still in the table, and only
   the table owner reaps, so the unreaped child pins the pid.
3. **smux `close_owned_children`** hangs up every pane that will end in
   `sosix_pty_close` (no owned transfer, not awaiting release, no
   `terminal_ref`, `pty_fd >= 0`) before closing any, but only when two or more
   such panes are in scope. Rollback and stop-all of the caret multi-launch
   adapter both reach it through `smux_kill_session`.
4. **EINTR**: `probe_pty_child_with` (shared by both lanes' `is_running`)
   retries EINTR (bounded, 64), drops the record only on a reap or ECHILD, and
   keeps it on any other failure so close still reaps.

Green: the three red tests pass (`cargo test -p simple-runtime --lib
value::pty`, 8/8).

Close time, 4 panes, `caret_smux_launch_team` + `caret_smux_stop_all`,
interpreter lane, Linux aarch64:

| children | base seed, base source | branch seed, branch source |
|---|---|---|
| 4 x `/bin/sh` | 3073 ms | 23 ms |
| 4 x SIGHUP-ignoring script | 4077 ms | 1059 ms |

Specs (`test --mode=interpreter --no-cache`), base seed on base source vs
branch seed on branch source — identical, pre-existing reds have the same
failing examples: caret_smux_multi_launch 6/6 -> 6/6, multi_caret_manager
13/13, pane_backend 15/15, cs_smux_launcher 2/2, smux_client_input 17/17,
smux_system 56/56, smux_pane_lifecycle 10/12, smux_live_multi_pane 1/4,
smux_sosix_boundary 2/3.

### Remaining

- **Runtime redeploy required.** A runtime without `rt_pty_hangup` stops with
  `unknown extern function: rt_pty_hangup` when a smux session with two or
  more PTY panes is torn down (unresolved externs are a hard error, so no
  capability probe can guard it). Measured: base seed on branch source runs
  caret_smux_multi_launch 3/6. Single-pane teardown never reaches the extern.
- Batch trade-off: a child that ignores SIGHUP but exits on master EOF loses
  its own grace in batch mode — its master closes only after the shared 1 s
  deadline, immediately followed by SIGKILL.
- The shared grace starts at the hangup pre-pass, so slow non-PTY cleanups
  earlier in the same `close_owned_children` loop (piped / owned-helper panes)
  also spend it; a PTY child that exits on EOF rather than SIGHUP can then be
  SIGKILLed after a single check. Close-on-exec is set with `fcntl` after
  `openpty`, not atomically, so a concurrent fork+exec on another thread can
  still briefly inherit a master.
- The out-of-band reap hazard recorded by PR #8885 (a generic
  `native_process_wait(pid)` on a PTY pid) is unchanged.
