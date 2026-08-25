# agent_workspace_spec

> Operator manages agent sessions and worktrees through LLM Caret.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# agent_workspace_spec

Operator manages agent sessions and worktrees through LLM Caret.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/agent_workspace_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Operator manages agent sessions and worktrees through LLM Caret.

An operator running several coding agents wants each agent isolated in its own
detached git worktree and visible in its own tmux pane, and wants to broadcast
one command to every agent pane at once. Everything runs on a private tmux
socket and a throwaway git repository so the operator's own tmux server and the
shared repository are never touched.

## Scenarios

### LLM Caret agent worktrees

#### gives each agent a detached worktree and removes it on detach

- Add a worktree for agent-a
   - Expected: added.status equals `ok`
- git lists the new tree; a second add is idempotent
   - Expected: worktree_add(ws, "agent-a").output equals `exists`
- Remove it; git no longer lists it
   - Expected: worktree_remove(ws, "agent-a").status equals `ok`
   - Expected: worktree_remove(ws, "agent-a").output equals `absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _scratch("wt")
dir_remove_all(root)
val repo = _fixture_repo(root)
val ws = agent_workspace("caret-wt-" + root.len().to_text(), repo, root + "/trees")

step("Add a worktree for agent-a")
val added = worktree_add(ws, "agent-a")
expect(added.status).to_equal("ok")
expect(dir_exists(worktree_path(ws, "agent-a"))).to_be(true)

step("git lists the new tree; a second add is idempotent")
expect(worktree_list(ws)).to_contain(worktree_path(ws, "agent-a"))
expect(worktree_add(ws, "agent-a").output).to_equal("exists")

step("Remove it; git no longer lists it")
expect(worktree_remove(ws, "agent-a").status).to_equal("ok")
expect(dir_exists(worktree_path(ws, "agent-a"))).to_be(false)
expect(worktree_remove(ws, "agent-a").output).to_equal("absent")
dir_remove_all(root)
```

</details>

#### reports a worktree add that git rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = agent_workspace("caret-wt-bad", "/nonexistent/repo", _scratch("bad"))
val r = worktree_add(ws, "agent-x")
expect(r.status).to_equal("error")
expect(r.reason).to_equal("worktree_add_failed")
```

</details>

### LLM Caret agent tmux sessions

#### broadcasts one command to every pane and each pane shows it

- Start a private session and split it into two panes
   - Expected: session_ensure(ws, root).status equals `ok`
   - Expected: pane_split(ws, "0", root).status equals `ok`
   - Expected: panes.len() equals `2`
- Send one marker command to each pane
   - Expected: reached.len() equals `2`
- Every pane independently prints the marker
- Killing the private server leaves no session
   - Expected: session_kill(ws).status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
val root = _scratch("tmux")
dir_remove_all(root)
dir_create_all(root)
val ws = agent_workspace("caret-bcast", root, root + "/trees")
session_kill(ws)

step("Start a private session and split it into two panes")
expect(session_ensure(ws, root).status).to_equal("ok")
expect(session_alive(ws)).to_be(true)
expect(pane_split(ws, "0", root).status).to_equal("ok")
val panes = list_panes(ws)
expect(panes.len()).to_equal(2)

step("Send one marker command to each pane")
val marker = "CARET_BCAST_" + root.len().to_text()
val reached = send_to_each_pane(ws, "echo " + marker + "_DONE")
expect(reached.len()).to_equal(2)

step("Every pane independently prints the marker")
for target in panes:
    expect(wait_for_pane_text(ws, target, marker + "_DONE", 5000)).to_be(true)

step("Killing the private server leaves no session")
expect(session_kill(ws).status).to_equal("ok")
expect(session_alive(ws)).to_be(false)
dir_remove_all(root)
```

</details>

#### attaches an agent as worktree plus window and detaches both

- Attach agent-b: worktree created, window named after the agent
   - Expected: agent_attach(ws, "agent-b", "").status equals `ok`
- Detach agent-b: window gone, worktree gone
   - Expected: agent_detach(ws, "agent-b").status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
val root = _scratch("attach")
dir_remove_all(root)
val repo = _fixture_repo(root)
val ws = agent_workspace("caret-attach", repo, root + "/trees")
session_kill(ws)

step("Attach agent-b: worktree created, window named after the agent")
expect(agent_attach(ws, "agent-b", "").status).to_equal("ok")
expect(dir_exists(worktree_path(ws, "agent-b"))).to_be(true)
val panes = list_panes(ws)
expect(panes).to_contain("caret-attach:agent-b.0")

step("Detach agent-b: window gone, worktree gone")
expect(agent_detach(ws, "agent-b").status).to_equal("ok")
var still_there = false
for p in list_panes(ws):
    if p == "caret-attach:agent-b.0":
        still_there = true
expect(still_there).to_be(false)
expect(dir_exists(worktree_path(ws, "agent-b"))).to_be(false)
session_kill(ws)
dir_remove_all(root)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
