# workspace_cli_system_spec

> Operator drives agent sessions and worktrees from the LLM Caret command line.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# workspace_cli_system_spec

Operator drives agent sessions and worktrees from the LLM Caret command line.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/workspace_cli_system_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Operator drives agent sessions and worktrees from the LLM Caret command line.

An operator supervising several coding agents uses
`simple run src/app/llm_caret/main.spl workspace <id> <command>` as the dev
toolset over the infrastructure: attach agents (one detached git worktree +
one tmux window each), broadcast a command to every agent pane, read a pane
back, and tear everything down. Every example here spawns the REAL CLI as a
child process against a throwaway git repository and a private tmux socket,
so the verdict is about the shipped command surface, not the library.

## Scenarios

### LLM Caret workspace CLI

#### prints usage and exits 2 when no command is given

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _cli("", cwd(), [])
expect(r.code).to_equal(2)
expect(r.out).to_contain("Usage: llm_caret workspace")
expect(r.out).to_contain("broadcast <cmd...>")
```

</details>

#### attaches three agents, isolates their worktrees, broadcasts, and tears down

- Attach agent-1, agent-2, agent-3 through the CLI
   - Expected: r.code equals `0`
- status lists one worktree and one pane per agent
   - Expected: status.code equals `0`
   - Expected: _lines_with(status.out, "worktree ").len() equals `4`
   - Expected: _lines_with(status.out, "pane ").len() equals `4`
- Each worktree is a real detached checkout and edits do not leak between them
   - Expected: head1.trim() equals ``
- broadcast reaches every pane and every agent pane shows the marker
   - Expected: b.code equals `0`
   - Expected: _lines_with(b.out, "sent ").len() equals `4`
   - Expected: w.code equals `0`
- capture returns the pane's scrollback
   - Expected: cap.code equals `0`
- detach removes window and worktree; kill leaves no session
   - Expected: d.code equals `0`
   - Expected: _lines_with(_cli(id, repo, ["panes"]).out, id + ":").len() equals `3`
   - Expected: _cli(id, repo, ["kill"]).code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
val root = _scratch("team")
dir_remove_all(root)
val repo = _fixture_repo(root)
val id = "cli-team"
session_kill(agent_workspace(id, repo, ""))

step("Attach agent-1, agent-2, agent-3 through the CLI")
for agent in ["agent-1", "agent-2", "agent-3"]:
    val r = _cli(id, repo, ["attach", agent])
    expect(r.code).to_equal(0)
    expect(r.out).to_contain("window " + id + ":" + agent)

step("status lists one worktree and one pane per agent")
val status = _cli(id, repo, ["status"])
expect(status.code).to_equal(0)
expect(status.out).to_contain("session " + id + " alive=true")
expect(_lines_with(status.out, "worktree ").len()).to_equal(4)
expect(_lines_with(status.out, "pane ").len()).to_equal(4)

step("Each worktree is a real detached checkout and edits do not leak between them")
val wt1 = repo + "/build/caret_worktrees/" + id + "/agent-1"
val wt2 = repo + "/build/caret_worktrees/" + id + "/agent-2"
expect(file_exists(wt1 + "/README.md")).to_be(true)
file_write(wt1 + "/only_in_agent_1.txt", "x\n")
expect(file_exists(wt2 + "/only_in_agent_1.txt")).to_be(false)
val (head1, _e1, _c1) = process_run("git", ["-C", wt1, "symbolic-ref", "-q", "HEAD"])
expect(head1.trim()).to_equal("")

step("broadcast reaches every pane and every agent pane shows the marker")
val b = _cli(id, repo, ["broadcast", "echo", "TEAM_BCAST_OK"])
expect(b.code).to_equal(0)
expect(_lines_with(b.out, "sent ").len()).to_equal(4)
for agent in ["agent-1", "agent-2", "agent-3"]:
    val w = _cli(id, repo, ["wait", id + ":" + agent, "TEAM_BCAST_OK", "8000"])
    expect(w.code).to_equal(0)
    expect(w.out).to_contain("found TEAM_BCAST_OK")

step("capture returns the pane's scrollback")
val cap = _cli(id, repo, ["capture", id + ":agent-2"])
expect(cap.code).to_equal(0)
expect(cap.out).to_contain("TEAM_BCAST_OK")

step("detach removes window and worktree; kill leaves no session")
val d = _cli(id, repo, ["detach", "agent-1"])
expect(d.code).to_equal(0)
expect(dir_exists(wt1)).to_be(false)
expect(_lines_with(_cli(id, repo, ["panes"]).out, id + ":").len()).to_equal(3)
expect(_cli(id, repo, ["kill"]).code).to_equal(0)
expect(session_alive(agent_workspace(id, repo, ""))).to_be(false)
dir_remove_all(root)
```

</details>

#### reports a failing worktree operation with a non-zero exit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _cli("cli-bad", "/nonexistent/repo", ["add", "agent-x"])
expect(r.code).to_equal(1)
expect(r.out).to_contain("error worktree_add_failed")
```

</details>

#### refuses a nested suite launch from a workspace-launched child

- The child inherits LLM_CARET_WORKSPACE_DEPTH=1 from its launcher
   - Expected: r.code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
step("The child inherits LLM_CARET_WORKSPACE_DEPTH=1 from its launcher")
env_set("LLM_CARET_WORKSPACE_DEPTH", "1")
val r = _cli("cli-nested", cwd(), ["suite", "test/01_unit/app/llm_caret/agent_vcs_spec.spl"])
env_set("LLM_CARET_WORKSPACE_DEPTH", "")
expect(r.code).to_equal(1)
expect(r.out).to_contain("error recursion_limit")
expect(session_alive(agent_workspace("cli-nested", cwd(), ""))).to_be(false)
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
