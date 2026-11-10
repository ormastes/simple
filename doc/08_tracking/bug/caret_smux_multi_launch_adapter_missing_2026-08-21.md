# Caret smux multi-launch adapter missing

Status: open

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
