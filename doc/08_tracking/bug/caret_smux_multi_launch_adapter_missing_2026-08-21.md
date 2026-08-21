# Caret smux multi-launch adapter missing

Status: open

`src/app/llm_caret/multi_caret_manager.spl` owns a bounded provider batch,
rejects over-capacity admission before spawn, rolls back partial launch, and
derives an embedded terminal pane view from parent-owned process records. Poll
and stop remain parent-only lifecycle transitions. This satisfies the separate
`caret-multi-manager-launch` gate.

It does not call or own `os.apps.smux`, create a production smux session, bind
child PTYs to smux panes, or prove capture/resize/stop cleanup. Therefore
`caret-smux-multi-launch` remains TODO. Unblock it with an `os.apps.smux`
adapter that binds the manager's bounded child set to real panes, keeps the
manager as sole PID owner, and has executable launch/capture/resize/cancel/stop
evidence with no leaked children.
