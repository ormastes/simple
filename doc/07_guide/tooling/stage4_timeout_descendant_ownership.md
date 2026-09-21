# Stage 4 timeout descendant ownership

Stage 4 runs each matrix worker through `run-process-group-timeout.shs`. That
outer supervisor owns the worker session, cancellation, escalation, and reap.
The three command helpers inside a worker must therefore keep GNU `timeout` in
the foreground process group. A nested `timeout` group would escape the outer
supervisor's group cancellation.

Use `timeout --foreground -k 15s ...` in `run_logged`, `run_logged_append`, and
`run_logged_with_input`. The command still receives the helper deadline and
KILL escalation. The outer supervisor can also cancel the complete worker tree
on INT, TERM, or HUP.

The focused contract test starts a real acknowledged descendant through each
helper, cancels the outer supervisor, waits for its reap, and rejects a live or
zombie descendant before accepting scheduler state cleanup. Do not replace the
runtime assertion with a source-only count or a PID-only worker assertion.

