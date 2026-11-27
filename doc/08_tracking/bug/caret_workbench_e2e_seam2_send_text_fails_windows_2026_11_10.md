# caret_workbench_e2e seam 2: smux_send_text fails on Windows (2026-11-10)

**Status:** open. Pre-existing; masked by the seam-1 `.shs` exec failure
(`caret_workbench_e2e_spec` could never get past seam 1 on Windows to expose
it). Seam 1 is fixed in this branch; seam 2 is now the Windows blocker.

## Symptom

`test/03_system/app/llm_caret/caret_workbench_e2e_spec.spl` example 1 fails
with `expected false to equal true` (actual-first matcher phrasing: a
`to_equal(true)` received `false`). Instrumented breadcrumbs show execution
reaches the teardown with every instrumented point green:

- seam 1: manager status `running`, both stub children real pids, stopped clean
- `smux_pane_spawn(s, w, p, "/bin/sh", ["-c", "while read l; do echo \"GOT:$l\"; done"])` -> `is_ok() == true`
- teardown: `process_is_running(pid) == false` for both manager children

The one un-instrumented `to_equal(true)` before the teardown is
`smux_send_text(s.id, w.id, p.id, NONCE + "\n").is_ok()` (line ~123).

## Isolation

A standalone replica (fresh smux session, same spawn + send) reports
`send_ok=true` and echoes the nonce fine — so the send path works in isolation
and fails only in the e2e's full context (two manager stub children alive +
the pane child). Suspect the interaction of the async-inherit manager children
with the piped pane child's stdin write on Windows, or a pane-service state
limit reached only with the full team attached.

## Evidence artifacts

- `build/nb/seam1_evidence.txt` (worktree run): `status=running ... [pid=16532
  started] [pid=22196 started] stopped=stopped/processes_stopped`
- breadcrumb probe: last crumb `6_running0=false running1=false`

The spec also lingers ~60 s after the failure: some child outlives the run
(the pane's `while read` sh if `smux_close_pane` misses it, or the reap wait
at process exit).

## Fix direction

Instrument `smux_send_text`'s error string in the spec (it returns
`Result<_, text>` — the e2e asserts `is_ok()` and discards the reason), then
trace the service-side write on Windows with a live team attached. Do not
weaken the oracle: the nonce round-trip is the point of seam 2.
