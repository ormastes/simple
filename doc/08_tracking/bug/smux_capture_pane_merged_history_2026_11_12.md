# smux capture_pane returns merged history: own-pane exclusion test false-positives

Date: 2026-11-12
Status: open, diagnosed to component boundary
Owner: unassigned

## Symptom

`test/01_unit/app/llm_caret/agent_workspace_spec.spl` example
"smux: a pane never receives the broadcast issued by the CLI running inside it"
fails consistently (reproduced 3/3) on this Windows host:

```
expect(capture_pane(ws, id + ":owner").contains("OWN_SKIPPED")).to_be(false)
  -> expected false to equal true
```

The full llm_caret unit sweep is otherwise green after #8644; this is the
last red.

## Diagnosis (evidence from the test itself)

1. The CLI broadcast DID exclude its own pane at the send level: the test's
   `expect(capture_pane(owner)).not_to_contain("sent " + id + ":owner.0")`
   PASSES — the owner pane shows the send-report "sent <id>:other.0" and no
   "sent <id>:owner.0".
2. The bystander pane genuinely received and executed the broadcast
   (`other_saw` passes: "OWN_SKIPPED" appears in <id>:other).
3. Yet the OWNER pane capture ALSO contains "OWN_SKIPPED" — the EVALUATED
   form. The owner pane's scrollback only carries the UNEVALUATED typed text
   `OWN_$(echo SKIPPED)` (single-quoted through the owner shell), so an
   evaluated "OWN_SKIPPED" in the owner pane means the echo actually ran
   there.

## Ruled out

- Own-pane exclusion in `agent_workspace.send_to_each_pane` /
  `list_panes_except` (`p.target != skip and p.window_id != skip` vs
  `SMUX_PANE`): working per the send-report evidence.
- Merged capture history: `service.spl capture_history_joined` is per-pane
  (`self.screen`, `self.pane.id`), and `smux_remote` history-joined reads
  the focused (w.id, p.id) — the capture path is pane-scoped.
- The broadcast CLI's own report: it printed only "sent <id>:other.0".

## Open question

How did the evaluated `OWN_SKIPPED` enter the OWNER pane when the CLI only
sent to <id>:other.0? Suspects not yet instrumented: (a) an attach/echo path
that re-types the command into the attaching pane after the CLI exits;
(b) smux `send` fan-out across a window's panes when the target pane id is
stale; (c) the owner pane's `exec sleep 300` repaint re-evaluating a
pending input line. Live smux instrumentation of the owner pane's input
journal vs the service's send journal will distinguish these.

## Reproduce

```
bin/simple test test/01_unit/app/llm_caret/agent_workspace_spec.spl --mode=interpreter
```

(requires `sh` on PATH for the pane shells; backend auto-detects smux.)

## Fix direction

Make `history-joined` (or the capture path) honor the selected pane in the
smux owner; add a unit row pinning that `history-joined` after
`select-pane X` excludes other panes' lines.
