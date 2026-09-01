# agent_workspace_spec

> Operator manages agent sessions and worktrees through LLM Caret.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gives each agent a detached worktree and removes it on detach
- Add a worktree for agent-a
   - Expected: added.status equals `ok`
- git lists the new tree; a second add is idempotent
   - Expected: worktree_add(ws, "agent-a").output equals `exists`
- Remove it; git no longer lists it
   - Expected: worktree_remove(ws, "agent-a").status equals `ok`
   - Expected: worktree_remove(ws, "agent-a").output equals `absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("gives each agent a detached worktree and removes it on detach")
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

- reports a worktree add that git rejected
   - Expected: r.status equals `error`
   - Expected: r.reason equals `worktree_add_failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports a worktree add that git rejected")
val ws = agent_workspace("caret-wt-bad", "/nonexistent/repo", _scratch("bad"))
val r = worktree_add(ws, "agent-x")
expect(r.status).to_equal("error")
expect(r.reason).to_equal("worktree_add_failed")
```

</details>

### LLM Caret agent tmux sessions

#### broadcasts one command to every pane and each pane shows it

- broadcasts one command to every pane and each pane shows it
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

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("broadcasts one command to every pane and each pane shows it")
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

- attaches an agent as worktree plus window and detaches both
- Attach agent-b: worktree created, window named after the agent
   - Expected: agent_attach(ws, "agent-b", "").status equals `ok`
- Detach agent-b: window gone, worktree gone
   - Expected: agent_detach(ws, "agent-b").status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("attaches an agent as worktree plus window and detaches both")
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

### LLM Caret workspace recursion protection

#### refuses to launch a suite from inside a workspace-launched child

- refuses to launch a suite from inside a workspace-launched child
- A fresh process is at depth 0 and stamps depth 1 on what it spawns
   - Expected: workspace_depth() equals `0`
   - Expected: with_depth("echo hi") equals `LLM_CARET_WORKSPACE_DEPTH=1 echo hi`
   - Expected: with_depth("") equals ``
- At depth 1 the suite launch is refused before tmux is touched
   - Expected: r.status equals `error`
   - Expected: r.reason equals `recursion_limit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses to launch a suite from inside a workspace-launched child")
step("A fresh process is at depth 0 and stamps depth 1 on what it spawns")
env_set("LLM_CARET_WORKSPACE_DEPTH", "")
expect(workspace_depth()).to_equal(0)
expect(depth_exceeded()).to_be(false)
expect(with_depth("echo hi")).to_equal("LLM_CARET_WORKSPACE_DEPTH=1 echo hi")
expect(with_depth("")).to_equal("")

step("At depth 1 the suite launch is refused before tmux is touched")
env_set("LLM_CARET_WORKSPACE_DEPTH", "1")
expect(depth_exceeded()).to_be(true)
val ws = agent_workspace("caret-depth", cwd(), _scratch("depth"))
val r = launch_caret_suite(ws, cwd(), "test/x_spec.spl")
expect(r.status).to_equal("error")
expect(r.reason).to_equal("recursion_limit")
expect(session_alive(ws)).to_be(false)
env_set("LLM_CARET_WORKSPACE_DEPTH", "")
```

</details>

#### never broadcasts into the pane it is running from

- never broadcasts into the pane it is running from
   - Expected: session_ensure(ws, root).status equals `ok`
   - Expected: pane_split(ws, "0", root).status equals `ok`
- Pretend this process lives in the first pane (tmux sets TMUX_PANE)
- A broadcast reaches every OTHER pane only
   - Expected: reached.len() equals `1`
   - Expected: list_panes(ws).len() equals `2`
   - Expected: list_panes_except(ws, own).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("never broadcasts into the pane it is running from")
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
val root = _scratch("ownpane")
dir_remove_all(root)
dir_create_all(root)
val ws = agent_workspace("caret-own", root, root + "/trees")
session_kill(ws)
expect(session_ensure(ws, root).status).to_equal("ok")
expect(pane_split(ws, "0", root).status).to_equal("ok")

step("Pretend this process lives in the first pane (tmux sets TMUX_PANE)")
val (ids, _e, _c) = process_run("tmux", ["-L", ws.socket, "list-panes", "-s",
    "-t", ws.session, "-F", "#" + "{" + "pane_id" + "}"])
val own = ids.split("\n")[0].trim()
expect(own.starts_with("%")).to_be(true)
env_set("TMUX_PANE", own)

step("A broadcast reaches every OTHER pane only")
val reached = send_to_each_pane(ws, "echo OWN_PANE_SKIPPED")
expect(reached.len()).to_equal(1)
expect(list_panes(ws).len()).to_equal(2)
expect(list_panes_except(ws, own).len()).to_equal(1)
env_set("TMUX_PANE", "")
session_kill(ws)
dir_remove_all(root)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c79281efad929db3e9aaf394c4ffc803109fa33f61eac82116d440c50cdb4076`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c79281efad929db3e9aaf394c4ffc803109fa33f61eac82116d440c50cdb4076`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c79281efad929db3e9aaf394c4ffc803109fa33f61eac82116d440c50cdb4076`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/llm_caret/agent_workspace_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/agent_workspace_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/agent_workspace_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/agent_workspace_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/agent_workspace_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/agent_workspace_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives each agent a detached worktree and removes it on detach' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/agent_workspace_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a worktree add that git rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/agent_workspace_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'broadcasts one command to every pane and each pane shows it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
