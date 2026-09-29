# workspace_recovery_system_spec

> Operator re-runs and mis-types workspace commands without breaking the team.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# workspace_recovery_system_spec

Operator re-runs and mis-types workspace commands without breaking the team.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/workspace_recovery_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Operator re-runs and mis-types workspace commands without breaking the team.

Real operators repeat commands (a second `attach` for an agent that is already
attached, `session_ensure` from two shells), leave stale directories behind, and
address agents that do not exist. Each scenario here drives the real
infrastructure -- a private tmux socket and a throwaway git repository -- and
asserts what the operator can observe afterwards: how many windows and
worktrees exist, whether the session survived, and what the CLI's exit status
and message were.

## Scenarios

### LLM Caret workspace recovery and idempotency

#### session_ensure twice yields one session and no second window

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- session_ensure twice yields one session and no second window
- First ensure creates the session with a single bootstrap pane
   - Expected: session_ensure(ws, repo).status equals `ok`
   - Expected: list_panes(ws).len() equals `1`
- Second ensure reports the existing session and adds nothing
   - Expected: again.status equals `ok`
   - Expected: again.output equals `exists`
   - Expected: list_panes(ws).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("session_ensure twice yields one session and no second window")
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
val root = _scratch("ensure")
dir_remove_all(root)
val repo = _fixture_repo(root)
val ws = agent_workspace("rec-ensure-" + current_time_ms().to_text(), repo, root + "/trees")
session_kill(ws)

step("First ensure creates the session with a single bootstrap pane")
expect(session_ensure(ws, repo).status).to_equal("ok")
expect(session_alive(ws)).to_be(true)
expect(list_panes(ws).len()).to_equal(1)

step("Second ensure reports the existing session and adds nothing")
val again = session_ensure(ws, repo)
expect(again.status).to_equal("ok")
expect(again.output).to_equal("exists")
expect(list_panes(ws).len()).to_equal(1)

session_kill(ws)
expect(session_alive(ws)).to_be(false)
dir_remove_all(root)
```

</details>

#### attaching the same agent twice keeps one worktree and one window

- attaching the same agent twice keeps one worktree and one window
- First attach: one worktree registered, one agent window (+ bootstrap window 0)
   - Expected: agent_attach(ws, "agent-a", "").status equals `ok`
   - Expected: worktree_list(ws).len() equals `2`
   - Expected: _windows_named(ws, "agent-a") equals `1`
   - Expected: list_panes(ws).len() equals `2`
- Second attach of the same agent is idempotent: still one worktree, still one window
   - Expected: again.status equals `ok`
   - Expected: again.output equals `exists`
   - Expected: worktree_list(ws).len() equals `2`
   - Expected: _windows_named(ws, "agent-a") equals `1`
   - Expected: list_panes(ws).len() equals `2`
- One detach after two attaches leaves zero windows and no worktree for that agent
   - Expected: agent_detach(ws, "agent-a").status equals `ok`
   - Expected: _windows_named(ws, "agent-a") equals `0`
   - Expected: list_panes(ws).len() equals `1`
- A second detach is now the unknown-agent error, and the session survives
   - Expected: agent_detach(ws, "agent-a").reason equals `kill_window_failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("attaching the same agent twice keeps one worktree and one window")
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
val root = _scratch("double")
dir_remove_all(root)
val repo = _fixture_repo(root)
val ws = agent_workspace("rec-double-" + current_time_ms().to_text(), repo, root + "/trees")
session_kill(ws)

step("First attach: one worktree registered, one agent window (+ bootstrap window 0)")
expect(agent_attach(ws, "agent-a", "").status).to_equal("ok")
expect(_contains(worktree_list(ws), worktree_path(ws, "agent-a"))).to_be(true)
expect(worktree_list(ws).len()).to_equal(2)
expect(_windows_named(ws, "agent-a")).to_equal(1)
expect(list_panes(ws).len()).to_equal(2)

step("Second attach of the same agent is idempotent: still one worktree, still one window")
val again = agent_attach(ws, "agent-a", "")
expect(again.status).to_equal("ok")
expect(again.output).to_equal("exists")
expect(worktree_list(ws).len()).to_equal(2)
expect(_windows_named(ws, "agent-a")).to_equal(1)
expect(list_panes(ws).len()).to_equal(2)

step("One detach after two attaches leaves zero windows and no worktree for that agent")
expect(agent_detach(ws, "agent-a").status).to_equal("ok")
expect(_windows_named(ws, "agent-a")).to_equal(0)
expect(list_panes(ws).len()).to_equal(1)
expect(_contains(worktree_list(ws), worktree_path(ws, "agent-a"))).to_be(false)
expect(dir_exists(worktree_path(ws, "agent-a"))).to_be(false)

step("A second detach is now the unknown-agent error, and the session survives")
expect(agent_detach(ws, "agent-a").reason).to_equal("kill_window_failed")
expect(session_alive(ws)).to_be(true)

session_kill(ws)
dir_remove_all(root)
```

</details>

#### reports a hand-made directory at the worktree path honestly: it is not a git worktree

- reports a hand-made directory at the worktree path honestly: it is not a git worktree
- An operator (or a crashed run) left a plain directory where agent-p's worktree would go
- worktree_add refuses with error path_occupied: a directory git does not list is not a worktree
   - Expected: r.status equals `error`
   - Expected: r.reason equals `path_occupied`
- git still does not know it, and the operator's directory was neither claimed nor deleted
   - Expected: worktree_list(ws).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports a hand-made directory at the worktree path honestly: it is not a git worktree")
val root = _scratch("plaindir")
dir_remove_all(root)
val repo = _fixture_repo(root)
val ws = agent_workspace("rec-plaindir-" + current_time_ms().to_text(), repo, root + "/trees")

step("An operator (or a crashed run) left a plain directory where agent-p's worktree would go")
val path = worktree_path(ws, "agent-p")
dir_create_all(path)
file_write(path + "/stale.txt", "not a worktree\n")
expect(dir_exists(path)).to_be(true)
expect(_contains(worktree_list(ws), path)).to_be(false)

step("worktree_add refuses with error path_occupied: a directory git does not list is not a worktree")
val r = worktree_add(ws, "agent-p")
expect(r.status).to_equal("error")
expect(r.reason).to_equal("path_occupied")

step("git still does not know it, and the operator's directory was neither claimed nor deleted")
expect(_contains(worktree_list(ws), path)).to_be(false)
expect(worktree_list(ws).len()).to_equal(1)
expect(file_exists(path + "/README.md")).to_be(false)
expect(file_exists(path + "/stale.txt")).to_be(true)
dir_remove_all(root)
```

</details>

#### reports a plain file at the worktree path as path_occupied and leaves the file alone

- reports a plain file at the worktree path as path_occupied and leaves the file alone
- A regular file sits exactly where agent-f's worktree would be created
- worktree_add refuses with error path_occupied instead of claiming or replacing it
   - Expected: r.status equals `error`
   - Expected: r.reason equals `path_occupied`
   - Expected: worktree_list(ws).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports a plain file at the worktree path as path_occupied and leaves the file alone")
val root = _scratch("plainfile")
dir_remove_all(root)
val repo = _fixture_repo(root)
val ws = agent_workspace("rec-plainfile-" + current_time_ms().to_text(), repo, root + "/trees")

step("A regular file sits exactly where agent-f's worktree would be created")
val path = worktree_path(ws, "agent-f")
dir_create_all(root + "/trees")
file_write(path, "not a directory\n")
expect(file_exists(path)).to_be(true)

step("worktree_add refuses with error path_occupied instead of claiming or replacing it")
val r = worktree_add(ws, "agent-f")
expect(r.status).to_equal("error")
expect(r.reason).to_equal("path_occupied")
expect(file_exists(path)).to_be(true)
expect(_contains(worktree_list(ws), path)).to_be(false)
expect(worktree_list(ws).len()).to_equal(1)
dir_remove_all(root)
```

</details>

#### a second worktree_add for a REAL worktree is still reported as exists

- a second worktree_add for a REAL worktree is still reported as exists
- First add registers the worktree with git
   - Expected: worktree_add(ws, "agent-r").status equals `ok`
- Second add is idempotent: ok/'exists', still one registered worktree
   - Expected: again.status equals `ok`
   - Expected: again.output equals `exists`
   - Expected: worktree_list(ws).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a second worktree_add for a REAL worktree is still reported as exists")
val root = _scratch("realtwice")
dir_remove_all(root)
val repo = _fixture_repo(root)
val ws = agent_workspace("rec-realtwice-" + current_time_ms().to_text(), repo, root + "/trees")

step("First add registers the worktree with git")
expect(worktree_add(ws, "agent-r").status).to_equal("ok")
expect(_contains(worktree_list(ws), worktree_path(ws, "agent-r"))).to_be(true)

step("Second add is idempotent: ok/'exists', still one registered worktree")
val again = worktree_add(ws, "agent-r")
expect(again.status).to_equal("ok")
expect(again.output).to_equal("exists")
expect(worktree_list(ws).len()).to_equal(2)
dir_remove_all(root)
```

</details>

#### detaching an unknown agent is an error and leaves the session and its agents intact

- detaching an unknown agent is an error and leaves the session and its agents intact
- One real agent is attached
   - Expected: agent_attach(ws, "agent-real", "").status equals `ok`
   - Expected: list_panes(ws).len() equals `2`
- Detaching an agent that was never attached reports an error, not success
   - Expected: r.status equals `error`
   - Expected: r.reason equals `kill_window_failed`
- A name that is only a PREFIX of the real agent is also unknown (tmux -t matches prefixes)
   - Expected: agent_detach(ws, "agent").status equals `error`
- The session and the real agent's window and worktree are untouched
   - Expected: _windows_named(ws, "agent-real") equals `1`
   - Expected: list_panes(ws).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detaching an unknown agent is an error and leaves the session and its agents intact")
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
val root = _scratch("unknown")
dir_remove_all(root)
val repo = _fixture_repo(root)
val ws = agent_workspace("rec-unknown-" + current_time_ms().to_text(), repo, root + "/trees")
session_kill(ws)

step("One real agent is attached")
expect(agent_attach(ws, "agent-real", "").status).to_equal("ok")
expect(list_panes(ws).len()).to_equal(2)

step("Detaching an agent that was never attached reports an error, not success")
val r = agent_detach(ws, "agent-ghost")
expect(r.status).to_equal("error")
expect(r.reason).to_equal("kill_window_failed")

step("A name that is only a PREFIX of the real agent is also unknown (tmux -t matches prefixes)")
expect(agent_detach(ws, "agent").status).to_equal("error")

step("The session and the real agent's window and worktree are untouched")
expect(session_alive(ws)).to_be(true)
expect(_windows_named(ws, "agent-real")).to_equal(1)
expect(list_panes(ws).len()).to_equal(2)
expect(_contains(worktree_list(ws), worktree_path(ws, "agent-real"))).to_be(true)
expect(dir_exists(worktree_path(ws, "agent-real"))).to_be(true)

agent_detach(ws, "agent-real")
session_kill(ws)
dir_remove_all(root)
```

</details>

#### broadcast on a dead session reaches no pane and the CLI exits 1 with error no_panes

- broadcast on a dead session reaches no pane and the CLI exits 1 with error no_panes
- Library: send_to_each_pane on a session that does not exist reaches zero panes
   - Expected: send_to_each_pane(ws, "echo never").len() equals `0`
- CLI: `workspace <id> broadcast ...` exits 1 and prints `error no_panes`
   - Expected: code equals `1`
- The failed broadcast did not create a session as a side effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("broadcast on a dead session reaches no pane and the CLI exits 1 with error no_panes")
if not tmux_available():
    pending("BLOCKED: tmux not installed on this host")
    return
val root = _scratch("dead")
dir_remove_all(root)
val repo = _fixture_repo(root)
val id = "rec-dead-" + current_time_ms().to_text()
val ws = agent_workspace(id, repo, root + "/trees")
session_kill(ws)
expect(session_alive(ws)).to_be(false)

step("Library: send_to_each_pane on a session that does not exist reaches zero panes")
expect(send_to_each_pane(ws, "echo never").len()).to_equal(0)

step("CLI: `workspace <id> broadcast ...` exits 1 and prints `error no_panes`")
val (out, err, code) = process_run("bin/simple",
    ["run", CLI, "workspace", id, "broadcast", "echo", "never", "--repo", repo])
expect(code).to_equal(1)
expect(out + err).to_contain("error no_panes")

step("The failed broadcast did not create a session as a side effect")
expect(session_alive(ws)).to_be(false)
dir_remove_all(root)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `529a2878876f1627b9ea7a18e57b11c3998208d3af561606947a46dea2ef431e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `529a2878876f1627b9ea7a18e57b11c3998208d3af561606947a46dea2ef431e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `529a2878876f1627b9ea7a18e57b11c3998208d3af561606947a46dea2ef431e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/llm_caret/workspace_recovery_system_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/workspace_recovery_system_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/workspace_recovery_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/workspace_recovery_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/workspace_recovery_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/workspace_recovery_system_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'session_ensure twice yields one session and no second window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/workspace_recovery_system_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'attaching the same agent twice keeps one worktree and one window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/workspace_recovery_system_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a hand-made directory at the worktree path honestly: it is not a git worktree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
