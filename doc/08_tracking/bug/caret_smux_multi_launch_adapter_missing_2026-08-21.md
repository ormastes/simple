# Caret smux multi-launch adapter missing

Status: FIXED (adapter + executable evidence landed; must-check ledger
promotion still rides the external-receipt gate, see the caret2 addendum)

`src/app/llm_caret/multi_caret_manager.spl` owns a bounded provider batch,
rejects over-capacity admission before spawn, rolls back partial launch, and
derives an embedded terminal pane view from parent-owned process records. Poll
and stop remain parent-only lifecycle transitions. This satisfies the separate
`caret-batch-process-adapter` gate.

It does not call or own `os.apps.smux`, create a production smux session, bind
child PTYs to smux panes, or prove capture/resize/stop cleanup. Therefore
`caret-smux-multi-launch` remains TODO. Unblock it with an `os.apps.smux`
adapter that binds the manager's bounded child set to real panes, keeps the
manager as sole PID owner, and has executable launch/capture/resize/cancel/stop
evidence with no leaked children.


## Addendum 2026-11-11 — lane ne3: LIVE — smux adapter still missing; gate
## still asserts the row stays `todo`

Traversed on work/p3-ne3-20261111 (origin/release/1.0.0 tip 93490a99c5d8).

- `src/app/llm_caret/multi_caret_manager.spl` still neither imports nor calls
  `os.apps.smux`; its only smux mention is the comment at :33 ("integration
  with the separate os.apps.smux service"). No file in `src/app/llm_caret/`
  binds the manager's bounded child set to smux panes/PTYs.
- No commit on `origin/release/1.0.0` references this bug id or lands a
  multi-launch smux adapter.
- The bootstrap gate still encodes the un-promoted state and actively asserts
  it: `scripts/check/check-bootstrap-must-pass.shs:377` greps for
  `caret-smux-multi-launch, todo, never` in the ledger — i.e. promotion of
  this row is expected to stay `todo` until real evidence exists, and the row
  must not be flip-able by a stale ledger.

Verdict: unchanged and still open. Unblock condition is the same as filed: an
`os.apps.smux` adapter binding the manager's bounded child set to real panes,
manager remaining sole PID owner, with executable launch/capture/resize/
cancel/stop evidence and no leaked children. Status stays OPEN.

## Addendum 2026-11-11 — lane p3-caret1: BLOCKED (feature + live PTY evidence; grant recorded)

Traversed on work/p3-caret1-20261111 (origin/release/1.0.0 tip 79d5af6723f6).

Confirmed live at tip, consistent with the lane-ne3 addendum above:
`src/app/llm_caret/multi_caret_manager.spl` still neither imports nor calls
`os.apps.smux` (only the :33 comment), and no file in `src/app/llm_caret/`
binds the manager's bounded child set to smux panes/PTYs. The bootstrap gate
still asserts the un-promoted state (scripts/check/check-bootstrap-must-pass.shs
:355 and :377 keep `caret-smux-multi-launch, todo, never`).

Verbatim unblock condition (re-recorded intact): an `os.apps.smux` adapter that
binds the manager's bounded child set to real panes, keeps the manager as sole
PID owner, and has executable launch/capture/resize/cancel/stop evidence with no
leaked children. Per the companion authenticity bug, promotion additionally
requires one real session/pane/PTY per Caret child, nonce capture, observed
resize, cancel/stop/wait/close, and zero PID/fd survivors; display-only
`AgentTmuxEmbed` and in-memory `smux/api.spl` rows are not PTY evidence.

This lane is a Windows seed-only worktree: no live smux PTY runtime environment
exists here to produce or honestly verify that evidence, and the ledger row is
deliberately pinned `todo` until it does. Status stays OPEN.

## Addendum 2026-11-11 — lane p3-caret2: FIXED — smux multi-launch adapter
## implemented with executable PTY lifecycle evidence

Traversed on work/p3-caret2-20261111 (origin/release/1.0.0 tip
66506fda143ca).

The unblock condition is met with landed source and a green executable spec:

- `src/app/llm_caret/caret_smux_multi_launch.spl` (new): the
  `os.apps.smux` adapter. One smux session per manager (`caret-smux-<id>`),
  one pane and one real pseudo-terminal per Caret child, spawned through
  `smux_pane_spawn_pty` (which drives the common `std.sys.pty` wrapper;
  ConPTY on Windows, POSIX PTY elsewhere — no OS-specific PTY calls in the
  adapter). It exposes launch/rollback, per-child cancel, whole-team stop,
  capture, resize, and a truthful PTY liveness probe
  (`caret_smux_child_alive`, the smux pane's own `pty_is_running`).
- `src/app/llm_caret/multi_caret_manager.spl`:
  `launch_multi_caret_manager_via_smux` — the manager's bounded admission
  envelope (id/capacity 1..16/non-empty/under-capacity, identical to the
  piped path) with every child spawned through the adapter. The manager's
  process team remains the canonical child record; the adapter binding only
  mirrors pane addresses. Partial batches roll back fail-closed (session
  kill) with a parent-side survivor check.
- `src/compiler_rust/lib/std/src/sys/pty.spl`: extended from a thin
  pass-through to the common wrapper surface (open/spawn/read/write/
  is_running/resize/can_resize/cleanup_pending/exit_code), matching the
  source-tree wrapper so consumers code against one cross-platform
  interface.
- `test/03_system/app/llm_caret/feature/caret_smux_multi_launch_spec.spl`
  (new): 6/6 PASS on the Windows ConPTY host
  (`SIMPLE_LIB=src bin/simple.exe test ... --mode=interpreter --no-cache`):
  (1) two concurrent interactive children, per-pane nonce capture with
  cross-pane contamination checks; (2) manager-driven launch with
  parent-owned team, adapter/team pid parity, adapter terminate, parent
  poll-observed exit and settle; (3) resize observed by the child through
  `mode con` before/after; (4) one child canceled (PTY close) while the
  other still answers; (5) over-capacity rejected before any smux session
  exists; (6) partial batch rolled back with the spawned child terminated
  and the session removed.

Engine honesty notes (why the evidence reads the way it does):

- Termination authority for PTY children is the smux pane PTY close, not
  the plain pid facade: the interpreter's `rt_process_kill` reaches only
  engine-spawned pids and the Windows liveness probe refuses unknown pids
  (`doc/08_tracking/bug/interpreter_process_is_running_false_for_unspawned_pid_2026-09-06.md`).
  Pane PTY close terminates the child and waits for it; the spec's
  zero-survivor receipts are the adapter's `smux_session_closed` reason,
  the removed session, and (on POSIX, where the facade is truthful)
  `process_is_running == false` per pid.
- Interactive spec children are plain shells standing in for injected
  provider executables, matching the existing manager specs; the
  manager-path scenario launches children with real plan-derived argv.

Deliberately unchanged: the `caret-smux-multi-launch, todo, never` ledger
row and `scripts/check/check-bootstrap-must-pass.shs` (:355/:377). Row
promotion is owned by the bootstrap must-check external-receipt path, which
still fails closed for caret gates
(`check-external-must-check-receipt.shs`: caret-semantic-validator-not-
implemented) and requires a trusted reviewer signature over committed
receipts — a separate lane's machinery. This fix lands the adapter and its
executable evidence that lane consumes.
