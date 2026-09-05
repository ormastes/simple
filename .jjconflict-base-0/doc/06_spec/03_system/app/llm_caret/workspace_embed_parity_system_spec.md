# workspace_embed_parity_system_spec

> Operator's embedded tmux view mirrors the real agent panes, pid for pid.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# workspace_embed_parity_system_spec

Operator's embedded tmux view mirrors the real agent panes, pid for pid.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/workspace_embed_parity_system_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Operator's embedded tmux view mirrors the real agent panes, pid for pid.

LLM Caret shows agents inside the editor through a model-only embed
(`build_agent_tmux_embed` / `render_agent_tmux_tui`) that never owns a process.
The operator trusts that view only if it agrees with the real tmux server: one
rendered pane row per real agent pane, and the pid printed on each row is the
pid tmux reports for that pane -- a live process, verifiable with `kill -0`.
This scenario attaches real agents on a private socket, reads the pane pids
back from tmux itself, feeds them into the model, and compares the rendered TUI
against the server's pane list.

## Scenarios

### LLM Caret embedded tmux view parity with real panes

#### renders exactly one pane row per real agent pane with the pid tmux reports

- Attach four real agents, each running a long-lived process in its own pane
   - Expected: agent_attach(ws, agent, "sleep 300").status equals `ok`
   - Expected: list_panes(ws).len() equals `AGENTS.len() + 1`
- Read the agent panes' pids back from the tmux server (window 0 is the session's bootstrap shell, not an agent)
   - Expected: agent_panes.len() equals `AGENTS.len()`
- Build the team model from those real pids and render the embedded view
   - Expected: team.status equals `started`
- The rendered TUI has exactly as many pane rows as real agent panes, and each row carries that pane's pid
   - Expected: _count_rows(tui) equals `agent_panes.len()`
- The model's session mirrors the server: one pane per agent
   - Expected: model_panes equals `agent_panes.len()`
- Tear down: after detach + kill every pane pid is gone and the session is dead
   - Expected: agent_detach(ws, agent).status equals `ok`
   - Expected: session_kill(ws).status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
val root = _scratch("team")
dir_remove_all(root)
val repo = _fixture_repo(root)
val id = "embed-parity-" + current_time_ms().to_text()
val ws = agent_workspace(id, repo, root + "/trees")
session_kill(ws)

step("Attach four real agents, each running a long-lived process in its own pane")
for agent in AGENTS:
    expect(agent_attach(ws, agent, "sleep 300").status).to_equal("ok")
expect(session_alive(ws)).to_be(true)
expect(list_panes(ws).len()).to_equal(AGENTS.len() + 1)

step("Read the agent panes' pids back from the tmux server (window 0 is the session's bootstrap shell, not an agent)")
var agent_panes: [RealPane] = []
for pane in _real_panes(ws.socket, ws.session):
    for agent in AGENTS:
        if pane.window == agent:
            agent_panes = agent_panes + [pane]
expect(agent_panes.len()).to_equal(AGENTS.len())
for pane in agent_panes:
    expect(pane.pid).to_be_greater_than(1)
    expect(_pid_alive(pane.pid)).to_be(true)

step("Build the team model from those real pids and render the embedded view")
var procs: [AgentProcess] = []
for pane in agent_panes:
    procs = procs + [AgentProcess(agent_id: pane.window, status: "started",
        reason: "tmux_pane", pid: pane.pid)]
val team = summarize_agent_team(id, procs)
expect(team.status).to_equal("started")
val usages: [AgentProcessUsage] = []
val embed = build_agent_tmux_embed(team, usages)
val tui = render_agent_tmux_tui(embed, team)

step("The rendered TUI has exactly as many pane rows as real agent panes, and each row carries that pane's pid")
expect(tui).to_contain("Team: " + id)
expect(_count_rows(tui)).to_equal(agent_panes.len())
var i = 0
while i < agent_panes.len():
    val pane = agent_panes[i]
    expect(tui).to_contain("pane[" + i.to_text() + "] " + pane.window + " pid=" + pane.pid.to_text() + " status=started")
    i = i + 1

step("The model's session mirrors the server: one pane per agent")
var model_panes = 0
for w in embed.session.windows:
    model_panes = model_panes + w.panes.len()
expect(model_panes).to_equal(agent_panes.len())

step("Tear down: after detach + kill every pane pid is gone and the session is dead")
for agent in AGENTS:
    expect(agent_detach(ws, agent).status).to_equal("ok")
expect(session_kill(ws).status).to_equal("ok")
expect(session_alive(ws)).to_be(false)
for pane in agent_panes:
    expect(_wait_for_exit(pane.pid, 5000)).to_be(true)
dir_remove_all(root)
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
