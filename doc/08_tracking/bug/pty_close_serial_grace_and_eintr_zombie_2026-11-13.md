# PTY close: serial per-pane grace on teardown, EINTR drops the child record

- **ID:** pty_close_serial_grace_and_eintr_zombie_2026-11-13
- **Severity:** P3
- **Status:** open
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
