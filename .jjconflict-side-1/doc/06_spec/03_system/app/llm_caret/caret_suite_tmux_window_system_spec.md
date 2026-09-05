# caret_suite_tmux_window_system_spec

> Operator launches an LLM Caret spec suite inside a tmux window.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# caret_suite_tmux_window_system_spec

Operator launches an LLM Caret spec suite inside a tmux window.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/caret_suite_tmux_window_system_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Operator launches an LLM Caret spec suite inside a tmux window.

An operator supervising agents from tmux wants the caret test suite to run in
its own window of the private agent session and to read the authoritative
`Results:` verdict straight off the pane, without leaving tmux. This scenario
launches a real `bin/simple test` in a tmux window on a private socket and
reads the verdict back from `capture-pane`.

## Scenarios

### LLM Caret suite runs inside a tmux window

#### launches the suite in a window and the pane shows the Results verdict

- Launch the caret suite in a dedicated tmux window
   - Expected: launched.status equals `ok`
   - Expected: target equals `caret-suite:caret_suite`
- Wait for the runner's authoritative per-file verdict on the pane
- The pane reports the suite passed, not merely finished
- Tear the private tmux server down
   - Expected: session_kill(ws).status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
val root = cwd()
dir_create_all(root + "/build/test-artifacts/llm_caret")
val ws = agent_workspace("caret-suite", root, root + "/build/test-artifacts/llm_caret/trees")
session_kill(ws)

step("Launch the caret suite in a dedicated tmux window")
val launched = launch_caret_suite(ws, root, SUITE)
expect(launched.status).to_equal("ok")
val target = launched.output
expect(target).to_equal("caret-suite:caret_suite")
expect(list_panes(ws)).to_contain("caret-suite:caret_suite.0")

step("Wait for the runner's authoritative per-file verdict on the pane")
val done = wait_for_pane_text(ws, target, "Results:", 240000)
expect(done).to_be(true)

step("The pane reports the suite passed, not merely finished")
val screen = capture_pane(ws, target)
expect(screen).to_contain("SPEC FILE VERDICT: " + SUITE)
expect(screen).to_contain("0 failed")
expect(screen).to_contain("PASS " + SUITE)

step("Tear the private tmux server down")
expect(session_kill(ws).status).to_equal("ok")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
