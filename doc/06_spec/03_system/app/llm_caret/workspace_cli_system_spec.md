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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prints usage and exits 2 when no command is given
   - Expected: r.code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prints usage and exits 2 when no command is given")
val r = _cli("", cwd(), [])
expect(r.code).to_equal(2)
expect(r.out).to_contain("Usage: llm_caret workspace")
expect(r.out).to_contain("broadcast <cmd...>")
```

</details>

#### attaches three agents, isolates their worktrees, broadcasts, and tears down

- attaches three agents, isolates their worktrees, broadcasts, and tears down
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

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("attaches three agents, isolates their worktrees, broadcasts, and tears down")
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

- reports a failing worktree operation with a non-zero exit
   - Expected: r.code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports a failing worktree operation with a non-zero exit")
val r = _cli("cli-bad", "/nonexistent/repo", ["add", "agent-x"])
expect(r.code).to_equal(1)
expect(r.out).to_contain("error worktree_add_failed")
```

</details>

#### refuses a nested suite launch from a workspace-launched child

- refuses a nested suite launch from a workspace-launched child
- The child inherits LLM_CARET_WORKSPACE_DEPTH=1 from its launcher
   - Expected: r.code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses a nested suite launch from a workspace-launched child")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `60cf500222d5ff1135b2f44e19ec6d0237e6c7215ec5540663747486472a2929`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60cf500222d5ff1135b2f44e19ec6d0237e6c7215ec5540663747486472a2929`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60cf500222d5ff1135b2f44e19ec6d0237e6c7215ec5540663747486472a2929`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/llm_caret/workspace_cli_system_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/workspace_cli_system_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/workspace_cli_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/workspace_cli_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/workspace_cli_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/workspace_cli_system_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints usage and exits 2 when no command is given' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/workspace_cli_system_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'attaches three agents, isolates their worktrees, broadcasts, and tears down' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/workspace_cli_system_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a failing worktree operation with a non-zero exit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
