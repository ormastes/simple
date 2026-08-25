# agent_team_workspace_system_spec

> Operator runs a team of long-lived agents, each isolated in its own worktree.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# agent_team_workspace_system_spec

Operator runs a team of long-lived agents, each isolated in its own worktree.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/agent_team_workspace_system_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Operator runs a team of long-lived agents, each isolated in its own worktree.

An operator supervising three coding agents attaches each one to the private
tmux session on socket `caret_ws_<id>` and lets every agent run a real,
long-lived process in its own pane (here: a heartbeat loop that appends to a
file inside the agent's detached git worktree every 200ms). The operator needs
proof that the agents are isolated (an agent's files only ever land in its own
tree), that one broadcast is EXECUTED by every agent shell, that detaching one
agent leaves the rest running, and that tearing the team down leaves no tmux
server on the socket and no worktree registered with git.

Every fact asserted here comes from the real system: files on disk written by
real shells inside real tmux panes, `git worktree list --porcelain`, and the
tmux server's own exit status on the private socket.

## Scenarios

### LLM Caret agent team lifecycle

#### runs three isolated heartbeat agents, broadcasts to all, survives one detach, and tears down cleanly

- Attach agent-1..3: one detached worktree + one interactive shell window each
   - Expected: r.status equals `ok`
   - Expected: list_panes(ws).len() equals `4`
- Each agent starts a real heartbeat loop that appends to a file in ITS worktree every 200ms
   - Expected: send_to_pane(ws, id + ":" + agent, _heartbeat_command(agent)).status equals `ok`
- Heartbeats keep growing: the loops are alive, not one-shot echoes
- Per-worktree isolation: an agent's heartbeat file exists only in its own tree, never in a sibling tree or the repo
- One broadcast is EXECUTED by every agent shell (lowercase command in, uppercase output out)
   - Expected: reached.len() equals `4`
- Detach agent-2 only: its window and worktree go away, the other two keep beating
   - Expected: agent_detach(ws, "agent-2").status equals `ok`
   - Expected: list_panes(ws).len() equals `3`
- Tear down: detach the remaining agents and kill the private server
   - Expected: agent_detach(ws, "agent-1").status equals `ok`
   - Expected: agent_detach(ws, "agent-3").status equals `ok`
   - Expected: session_kill(ws).status equals `ok`
- Nothing is left: session dead, no server answers on the socket, git registers only the main repo
   - Expected: trees.len() equals `1`
   - Expected: trees[0] equals `real_repo.trim()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 76 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
val run_id = current_time_ms().to_text()
val root = _scratch("lifecycle")
dir_remove_all(root)
val repo = _fixture_repo(root)
val id = "team-life-" + run_id
val ws = agent_workspace(id, repo, root + "/trees")
session_kill(ws)

step("Attach agent-1..3: one detached worktree + one interactive shell window each")
for agent in AGENTS:
    val r = agent_attach(ws, agent, "")
    expect(r.status).to_equal("ok")
    expect(file_exists(worktree_path(ws, agent) + "/README.md")).to_be(true)
expect(session_alive(ws)).to_be(true)
# 3 agent windows + the session's bootstrap window 0
expect(list_panes(ws).len()).to_equal(4)

step("Each agent starts a real heartbeat loop that appends to a file in ITS worktree every 200ms")
for agent in AGENTS:
    expect(send_to_pane(ws, id + ":" + agent, _heartbeat_command(agent)).status).to_equal("ok")
for agent in AGENTS:
    expect(_wait_for_beats(_heartbeat_file(worktree_path(ws, agent), agent), 10000)).to_be(true)

step("Heartbeats keep growing: the loops are alive, not one-shot echoes")
val before_1 = _beats(_heartbeat_file(worktree_path(ws, "agent-1"), "agent-1"))
sleep_ms(800)
expect(_beats(_heartbeat_file(worktree_path(ws, "agent-1"), "agent-1"))).to_be_greater_than(before_1)

step("Per-worktree isolation: an agent's heartbeat file exists only in its own tree, never in a sibling tree or the repo")
for writer in AGENTS:
    for tree_owner in AGENTS:
        val present = file_exists(_heartbeat_file(worktree_path(ws, tree_owner), writer))
        expect(present).to_be(writer == tree_owner)
    expect(file_exists(_heartbeat_file(repo, writer))).to_be(false)

step("One broadcast is EXECUTED by every agent shell (lowercase command in, uppercase output out)")
val marker_in = "bcast_" + run_id
val marker_out = "BCAST_" + run_id
val reached = send_to_each_pane(ws, "echo " + marker_in + " | tr a-z A-Z")
expect(reached.len()).to_equal(4)
for agent in AGENTS:
    expect(_contains(reached, id + ":" + agent + ".0")).to_be(true)
    expect(wait_for_pane_text(ws, id + ":" + agent, marker_out, 10000)).to_be(true)

step("Detach agent-2 only: its window and worktree go away, the other two keep beating")
expect(agent_detach(ws, "agent-2").status).to_equal("ok")
expect(dir_exists(worktree_path(ws, "agent-2"))).to_be(false)
expect(_contains(worktree_list(ws), worktree_path(ws, "agent-2"))).to_be(false)
expect(list_panes(ws).len()).to_equal(3)
val before_a1 = _beats(_heartbeat_file(worktree_path(ws, "agent-1"), "agent-1"))
val before_a3 = _beats(_heartbeat_file(worktree_path(ws, "agent-3"), "agent-3"))
sleep_ms(800)
expect(_beats(_heartbeat_file(worktree_path(ws, "agent-1"), "agent-1"))).to_be_greater_than(before_a1)
expect(_beats(_heartbeat_file(worktree_path(ws, "agent-3"), "agent-3"))).to_be_greater_than(before_a3)
expect(session_alive(ws)).to_be(true)

step("Tear down: detach the remaining agents and kill the private server")
expect(agent_detach(ws, "agent-1").status).to_equal("ok")
expect(agent_detach(ws, "agent-3").status).to_equal("ok")
expect(session_kill(ws).status).to_equal("ok")

step("Nothing is left: session dead, no server answers on the socket, git registers only the main repo")
expect(session_alive(ws)).to_be(false)
val (_o, _e, ls_code) = process_run("tmux", ["-L", ws.socket, "list-sessions"])
expect(ls_code).to_be_greater_than(0)
val trees = worktree_list(ws)
expect(trees.len()).to_equal(1)
# git prints the resolved path; the fixture may sit behind a symlinked cwd.
val (real_repo, _re, _rc) = process_run("realpath", ["-m", repo])
expect(trees[0]).to_equal(real_repo.trim())
for agent in AGENTS:
    expect(dir_exists(worktree_path(ws, agent))).to_be(false)
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
