# cs_live_agents_system_spec

> As an operator running the `cs` caret-suite dashboard I launch real coding

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cs_live_agents_system_spec

As an operator running the `cs` caret-suite dashboard I launch real coding

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/cs_live_agents_system_spec.spl` |
| Updated | 2026-10-03 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
As an operator running the `cs` caret-suite dashboard I launch real coding
agents — Claude Code, Codex, Kimi — each in its own terminal pane, type to the
selected one from the dashboard's input line, and watch it answer in the
right-hand half of the same window while the roster stays on the left.
This spec starts the REAL agent CLIs. It is for the maintainers of the
dashboard (`src/app/llm_caret/cs_dashboard.spl`), the pane backend
(`src/app/llm_caret/pane_backend.spl`) and smux (`src/os/apps/smux/`).
## Operator workflow
bin/simple test test/03_system/app/llm_caret/cs_live_agents_system_spec.spl
Each scenario: `/launch <agent>`, answer any first-run dialog with `/key`,
type a question, read the answer off the agent screen, `/kill` the pane.
## Compatibility and limitations
Needs `claude`, `codex` and `kimi` on PATH and signed in; on Windows they are
found as claude.exe / codex.cmd / kimi.exe. Without tmux (always on Windows)
the panes are smux panes on a real ConPTY. A missing or signed-out agent is a
FAILED scenario naming the agent, never a skip. Each scenario costs one short
model call.
## Verification guidance and troubleshooting
The oracle is a product the agent must COMPUTE (4711 x 3 = 14133): the typed
question holds only 4711, so the answer cannot be an echo of the input. If the
question sits in the agent's input box unanswered, Enter was not delivered as
its own keystroke; if the screen shows stale dialog text, the pane screen
model (`os.apps.smux.vt_screen`) missed an erase sequence.

## Scenarios

### cs dashboard drives live agents in panes

#### Claude Code answers a dashboard question in the right-hand pane

- Launch claude from the dashboard and type the question
- The pane was created for the agent
   - TUI capture: after_step
- Claude computed the answer, and it shows in the agent half of the frame
   - Expected: run.answered is true
- Killing the agent closes its pane


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CS-LIVE-001
step("Launch claude from the dashboard and type the question")
val run = drive_agent("cs-live-claude", "claude", 180)
step("The pane was created for the agent")
expect(run.launched).to_contain("launched a1 in pane")
step("Claude computed the answer, and it shows in the agent half of the frame")
expect(run.answered).to_equal(true)
expect(right_half(run.frame)).to_contain(ANSWER)
step("Killing the agent closes its pane")
expect(run.killed).to_contain("killed pane")
```

</details>

#### Codex answers a dashboard question in the right-hand pane

- Launch codex from the dashboard and type the question
- The pane was created for the agent
   - TUI capture: after_step
- Codex computed the answer, and it shows in the agent half of the frame
   - Expected: run.answered is true
- Killing the agent closes its pane


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CS-LIVE-002
step("Launch codex from the dashboard and type the question")
val run = drive_agent("cs-live-codex", "codex", 180)
step("The pane was created for the agent")
expect(run.launched).to_contain("launched a1 in pane")
step("Codex computed the answer, and it shows in the agent half of the frame")
expect(run.answered).to_equal(true)
expect(right_half(run.frame)).to_contain(ANSWER)
step("Killing the agent closes its pane")
expect(run.killed).to_contain("killed pane")
```

</details>

#### Kimi answers a dashboard question in the right-hand pane

- Launch kimi from the dashboard and type the question
- The pane was created for the agent
   - TUI capture: after_step
- Kimi computed the answer, and it shows in the agent half of the frame
   - Expected: run.answered is true
- Killing the agent closes its pane


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CS-LIVE-003
step("Launch kimi from the dashboard and type the question")
val run = drive_agent("cs-live-kimi", "kimi", 180)
step("The pane was created for the agent")
expect(run.launched).to_contain("launched a1 in pane")
step("Kimi computed the answer, and it shows in the agent half of the frame")
expect(run.answered).to_equal(true)
expect(right_half(run.frame)).to_contain(ANSWER)
step("Killing the agent closes its pane")
expect(run.killed).to_contain("killed pane")
```

</details>

#### rejects launching an unknown agent instead of opening a dead pane

- Launch a harness name the dashboard does not know
- The dashboard names the harnesses it can launch and opens no pane
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: outcome does not contain `launched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CS-LIVE-004
step("Launch a harness name the dashboard does not know")
val d = cs_refresh(cs_dashboard_new("cs-live-missing"))
val (_after, outcome) = _cmd(d, "/launch no-such-agent-cli-9f2")
step("The dashboard names the harnesses it can launch and opens no pane")
expect(outcome).to_contain("unknown harness")
expect(outcome).to_contain("claude, codex, kimi")
expect(outcome.contains("launched")).to_equal(false)
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
