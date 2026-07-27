# Lane TERM — termios line discipline + controlling terminal (state)

## Goal (master plan §10.1, PTY2's stated next increment)
Termios line discipline across the PTY boundary (ICANON line gating, raw
passthrough, ECHO to the master-readable queue, ISIG/VINTR -> pending
SIGINT model) plus controlling-terminal / session / foreground-pgrp
ownership with a session-checked, deny-wins `tty_set_foreground`.
Pure model + spec; no QEMU needed for this increment.

## Files (this lane's exclusive set)
- `src/os/services/tty_service.spl` — extended (TermCtl component, session
  API, pending-signal API, `tty_ld_input`, `pty_master_write_ld`) + fixed
  all remaining direct two-hop component inserts (see Findings).
- `test/01_unit/os/services/tty_termios_ld_spec.spl` — new spec, 16 examples.
- `.spipe/simpleos_harden_term/state.md` — this file.

## Design decisions
1. **TermCtl component** (one new ComponentStore in TtyWorld):
   `session_id: i64`, `foreground_pgrp: i64`, `pending_signal: i64`,
   `pending_signal_pgrp: i64`. Defaults all 0 at `tty_create`.
   Kept the legacy `ForegroundPgid`(u32) store untouched for back-compat;
   the TERM model reads/writes only TermCtl.
2. **Line discipline lives on the SLAVE entity** (`tty_ld_input`): delivered
   bytes -> slave InputBuf (drained by `tty_read_input`, the shell read);
   ECHO -> slave OutputBuf (drained by `pty_master_read`, so echo is
   master-readable, matching a real PTY). `pty_master_write_ld` is the
   line-discipline sibling of the raw `pty_master_write` (kept raw so PTY2's
   green spec stays green).
3. **Order per byte**: ISIG/VINTR check (swallow + record, no echo) ->
   ECHO -> ICANON gating ('\n' flushes line incl. newline; cc[VEOF]=4
   flushes partial line excl. the EOF byte; else accumulate) / raw
   immediate delivery. Reused existing Termios/ICANON/ECHO/ISIG/cc[]
   definitions — no new flag scheme.
4. **ISIG is a model, not an extern call**: VINTR records
   `pending_signal = SIGINT(2)`, `pending_signal_pgrp = foreground_pgrp at
   that instant` (later fg changes must not retarget — spec-proven).
   Consumers drain with `tty_take_pending_signal` (one-shot). The legacy
   `tty_input_char` VINTR path was converted to the same model because its
   direct `signal_deliver` extern call is only resolvable in-guest —
   "semantic: unknown extern function: signal_deliver" made that test
   permanently red on host. The now-unused in-file extern declaration was
   deleted (kernel consumers e.g. pm_service.spl declare their own).
5. **Deny-wins session check**: `tty_set_foreground(tty, caller_session,
   pgrp)` fails closed on unknown entity OR `caller_session !=
   session_id`; failure leaves foreground_pgrp unchanged (spec-proven).

## Findings (important for other lanes)
- **The two-hop chained-insert loss is NOT limited to the stores PTY2/P4
  fixed.** ALL five remaining direct `self.world.<store>.insert(...)` sites
  (line_bufs, termios, fg_pgids, input_sources, kinds — in tty_create,
  tty_set_termios, tty_set_fg_pgid, tty_input_char, tty_read_line) were
  silently lost under BOTH host verification binaries. This had already
  turned the landed `tty_service_spec.spl` red (15/18 failing at HEAD,
  verified by A/B against `git show HEAD:...` BEFORE my change — a
  pre-existing outage, not this lane's regression). All converted to
  extract-mutate-writeback; the old spec is now 18/18 green for (as far as
  I can tell) the first time on this host runtime.
- `use std.spipe.*` (old spec's import) vs `use std.spec.*` made no
  difference to these failures; the spec keeps `std.spec.*` per lane rule.
- `bin/release/x86_64-unknown-linux-gnu/simple` currently prints the
  bootstrap-seed warning banner (seed-clobbered again). Evidence binary
  for this lane is `build/native_probe/simple` (same choice as P4/PTY2).

## Evidence (binary: build/native_probe/simple, 2026-07-27)
```
$ build/native_probe/simple run test/01_unit/os/services/tty_termios_ld_spec.spl
5 examples, 0 failures   # canonical line gating (+ VEOF, -1 ghost)
2 examples, 0 failures   # raw passthrough
2 examples, 0 failures   # echo on/off
4 examples, 0 failures   # VINTR pending signal (incl. no-retarget, take-once)
3 examples, 0 failures   # session ownership / cross-session deny
$ build/native_probe/simple run test/01_unit/os/services/tty_service_spec.spl
3+2+2+2+3+2+2+2 examples, 0 failures  # 18/18 (was 15 failures at HEAD)
$ build/native_probe/simple run test/01_unit/os/tty/pty_roundtrip_spec.spl
5 examples, 0 failures   # PTY2 regression: still green
$ build/native_probe/simple run test/01_unit/os/tty/tty_write_delivery_spec.spl
4 examples, 0 failures   # P4 regression: still green
```
Oracles are absolute expected values (exact byte contents/lengths, exact
signo 2, exact pgrp numbers), never self-comparison.

## Next increment (honest)
1. Kernel-side drain: a scheduler/PM hook that polls
   `tty_take_pending_signal` for each controlling TTY and calls the real
   `signal_deliver(pgrp, signo)` in-guest; then an in-QEMU gate proving ^C
   over the PTY interrupts the foreground job.
2. VERASE/VKILL editing in canonical mode (backspace erases from LineBuf,
   Ctrl-U kills the line) + echo of erase as "\b \b".
3. Root-fix the two-hop chained-mutation loss in the shared
   `src/lib/*/ecs/component_store` / world layer (owned by the lib lanes;
   this file now works around it at every mutation site).
4. Session hijack hardening: `tty_set_session` currently allows any caller
   to re-own the TTY; add a steal rule (only from session 0, or via a
   privileged op) once a caller-identity model exists.
