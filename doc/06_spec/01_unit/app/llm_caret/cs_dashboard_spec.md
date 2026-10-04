# cs_dashboard_spec

> Purpose: Prove that running `cs` with no arguments gives me a usable multi-agent

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cs_dashboard_spec

Purpose: Prove that running `cs` with no arguments gives me a usable multi-agent

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/cs_dashboard_spec.spl` |
| Updated | 2026-10-03 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that running `cs` with no arguments gives me a usable multi-agent
dashboard - I can see at a glance whether the agent manager is reachable and how
many agents it holds, pick one out of the list and read its detail, switch or
maximize its pane, and type into a command line that always sits on the bottom
row. When something cannot be measured or reached, the dashboard must tell me so
instead of showing me a comfortable zero.
Audience: compiler and tooling engineers who maintain the caret-suite dashboard.
## Operator workflow
Run `./src/compiler_rust/target/bootstrap/simple run test/01_unit/app/llm_caret/cs_dashboard_spec.spl`
from the repo root; scenarios are in-process (no real tmux session is needed
except the deliberately-absent one used for the honest-state checks).
## Compatibility and limitations
Rendering scenarios pin an 80x14 (or 60x8) grid, so a deliberate layout change
updates both sides. Executable-resolution scenarios depend only on `sh` existing
on PATH; the honest-state scenarios poll a session name that never exists and
accept either a connected or disconnected verdict, never the un-polled one.
## Verification guidance and troubleshooting
A launch-scenario failure usually means the spec parser (`/launch` harness
table) changed; a bottom-row failure means `cs_render` stopped reserving the
input row. An honest-state failure indicates the refresh path began fabricating
measurements — treat that as a product defect, not a test artifact.

## Scenarios

### cs dashboard - launching agents

#### resolves a launch command to a real executable before spawning a pane

- A command that exists on PATH resolves to a path
   - Protocol capture: after_step
- Windows resolution tries runnable PATHEXT targets in priority order
- A command that exists nowhere resolves to empty, not to itself
   - Expected: cs_resolve_exe("no-such-binary-xyz-9f2") equals ``
- 'simple' resolves even though it is not on PATH, via the repo wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-001
step("A command that exists on PATH resolves to a path")
val sh = cs_resolve_exe("sh")
val cmd = cs_resolve_exe("cmd")
expect((sh + cmd).len()).to_be_greater_than(0)

step("Windows resolution tries runnable PATHEXT targets in priority order")
expect(windows_executable_names("agent")).to_equal(
    ["agent.exe", "agent.cmd", "agent.bat"])

step("A command that exists nowhere resolves to empty, not to itself")
expect(cs_resolve_exe("no-such-binary-xyz-9f2")).to_equal("")

step("'simple' resolves even though it is not on PATH, via the repo wrapper")
expect(cs_resolve_exe("simple")).to_contain("simple")
```

</details>

#### refuses a chat message for an agent that has no pane instead of dropping it

- Launch an agent, which starts with no pane attached
   - Protocol capture: after_step
- A bare message produces a chat action aimed at that agent
- Executing it reports the missing pane rather than succeeding
   - Expected: outcome does not contain `sent to`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-002
step("Launch an agent, which starts with no pane attached")
val d0 = cs_dashboard_new("cs-spec-session")
val (d1, launched) = cs_handle_command(d0, "/launch caret:glm")
expect(launched).to_contain("launch:")

step("A bare message produces a chat action aimed at that agent")
val (d2, action) = cs_handle_command(d1, "hello there")
expect(action).to_start_with("chat:")

step("Executing it reports the missing pane rather than succeeding")
val (d3, outcome) = cs_apply_action(d2, action)
expect(outcome).to_contain("has no pane yet")
expect(outcome.contains("sent to")).to_equal(false)
```

</details>

#### reports a malformed chat action rather than sending a partial line

- An action with no message body is rejected
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-002
step("An action with no message body is rejected")
val d = cs_dashboard_new("cs-spec-session")
val (_, outcome) = cs_apply_action(d, "chat:a1")
expect(outcome).to_contain("malformed chat action")
```

</details>

#### adds an agent I can see when I launch a valid short spec

- start with an empty dashboard
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: empty.agents.len() equals `0)  # oracle: a fresh dashboard starts with no agents`
   - Expected: empty.selected equals `-1)  # oracle: -1 is the explicit no-selection sentinel`
- launch caret:glm/glm-4.6
   - Expected: after.agents.len() equals `1)  # oracle: one launch command adds exactly one agent`
   - Expected: after.agents[0].spec equals `caret:glm/glm-4.6`
   - Expected: after.selected equals `0)  # oracle: the first agent is auto-selected at index 0`
- the new agent is honestly marked as not yet launched
   - Expected: after.agents[0].pid equals `-1)  # oracle: -1 means no process was ever spawned`
   - Expected: after.agents[0].rss_mb equals `-1)  # oracle: -1 means no measurement was taken`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-003
step("start with an empty dashboard")
val empty = cs_dashboard_new("caret")
expect(empty.agents.len()).to_equal(0)  # oracle: a fresh dashboard starts with no agents
expect(empty.selected).to_equal(-1)  # oracle: -1 is the explicit no-selection sentinel

step("launch caret:glm/glm-4.6")
val (after, answer) = cs_handle_command(empty, "/launch caret:glm/glm-4.6")
expect(after.agents.len()).to_equal(1)  # oracle: one launch command adds exactly one agent
expect(after.agents[0].spec).to_equal("caret:glm/glm-4.6")
expect(after.selected).to_equal(0)  # oracle: the first agent is auto-selected at index 0
expect(answer).to_contain("launch:")
expect(answer).to_contain("caret:glm/glm-4.6")

step("the new agent is honestly marked as not yet launched")
expect(after.agents[0].status).to_contain("pending")
expect(after.agents[0].pid).to_equal(-1)  # oracle: -1 means no process was ever spawned
expect(after.agents[0].rss_mb).to_equal(-1)  # oracle: -1 means no measurement was taken
```

</details>

#### tells me exactly what is wrong when I mistype a launch spec

- launch an unknown harness
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: after.agents.len() equals `0)  # oracle: a rejected spec must add no agent`
- a provider on a CLI harness is refused with the parser's own words
   - Expected: after2.agents.len() equals `0)  # oracle: a rejected spec must add no agent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-004
step("launch an unknown harness")
val d = cs_dashboard_new("caret")
val (after, answer) = cs_handle_command(d, "/launch claudee")
expect(after.agents.len()).to_equal(0)  # oracle: a rejected spec must add no agent
expect(answer).to_contain("unknown harness")
expect(answer).to_contain("claudee")

step("a provider on a CLI harness is refused with the parser's own words")
val (after2, answer2) = cs_handle_command(d, "/launch claude:kimi")
expect(after2.agents.len()).to_equal(0)  # oracle: a rejected spec must add no agent
expect(answer2).to_contain("does not take a provider")
```

</details>

#### builds a launch command line that matches the spec I typed

- a caret harness runs caret with its provider and model
   - Protocol capture: after_step
- a CLI harness runs its own binary with just the model
   - Expected: cli_argv[0] equals `claude`
- an invalid spec yields no command at all
   - Expected: cs_launch_argv("claudee").len() equals `0)  # oracle: an unparsable spec must produce no argv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-005
step("a caret harness runs caret with its provider and model")
val caret_argv = cs_launch_argv("caret:glm/glm-4.6")
expect(caret_argv).to_contain("--provider")
expect(caret_argv).to_contain("glm")
expect(caret_argv).to_contain("glm-4.6")

step("a CLI harness runs its own binary with just the model")
val cli_argv = cs_launch_argv("claude/opus")
expect(cli_argv[0]).to_equal("claude")
expect(cli_argv).to_contain("opus")

step("an invalid spec yields no command at all")
expect(cs_launch_argv("claudee").len()).to_equal(0)  # oracle: an unparsable spec must produce no argv
```

</details>

### cs dashboard - selecting and maximizing panes

#### moves the selection when I switch by number or by id

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: cs-dashboard-panes (expected show, folded, detail, or skip)


- launch three agents so the last one is selected
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: d.selected equals `2)  # oracle: the most recently launched agent holds the selection`
- switch by 1-based position
   - Expected: by_num.selected equals `0)  # oracle: position 1 maps to 0-based index 0`
- switch by agent id
   - Expected: by_id.selected equals `1)  # oracle: agent a2 sits at roster index 1`
- switching to something that is not there changes nothing
   - Expected: missing.selected equals `2)  # oracle: a failed switch must leave the selection untouched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-006
step("launch three agents so the last one is selected")
val d = _launched("caret", ["claude", "codex", "kimi"])
expect(d.selected).to_equal(2)  # oracle: the most recently launched agent holds the selection

step("switch by 1-based position")
val (by_num, _a) = cs_handle_command(d, "/switch 1")
expect(by_num.selected).to_equal(0)  # oracle: position 1 maps to 0-based index 0

step("switch by agent id")
val (by_id, _b) = cs_handle_command(d, "/switch a2")
expect(by_id.selected).to_equal(1)  # oracle: agent a2 sits at roster index 1

step("switching to something that is not there changes nothing")
val (missing, answer) = cs_handle_command(d, "/switch a9")
expect(missing.selected).to_equal(2)  # oracle: a failed switch must leave the selection untouched
expect(answer).to_contain("no such agent")
```

</details>

#### maximizes the pane of the agent that is taking my commands

- give two agents real panes and select the second
   - Protocol capture: after_step
- /max targets the SELECTED agent's pane, not the first one
- after switching to the first agent, /max targets its pane instead


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-007
step("give two agents real panes and select the second")
val base = _launched("caret", ["claude", "codex"])
val a1 = CsAgent(agent_id: "a1", spec: "claude", status: "running",
    pid: 111, pane_id: "%1", cpu_pct: 1.0, rss_mb: 10, detail: "one")
val a2 = CsAgent(agent_id: "a2", spec: "codex", status: "running",
    pid: 222, pane_id: "%2", cpu_pct: 2.0, rss_mb: 20, detail: "two")
val d = CsDashboard(session: base.session,
    manager_status: base.manager_status, agents: [a1, a2],
    selected: 1, input: "", log: [], screen: [])

step("/max targets the SELECTED agent's pane, not the first one")
val (_after, answer) = cs_handle_command(d, "/max")
expect(answer).to_contain("pane:zoom")
expect(answer).to_contain("%2")

step("after switching to the first agent, /max targets its pane instead")
val (switched, select_answer) = cs_handle_command(d, "/switch a1")
expect(select_answer).to_contain("pane:select")
expect(select_answer).to_contain("%1")
val (_after2, answer2) = cs_handle_command(switched, "/max")
expect(answer2).to_contain("%1")
```

</details>

#### refuses to maximize when I have not selected anything

- ask /max for a zoom with no agent selected
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-007
step("ask /max for a zoom with no agent selected")
val d = cs_dashboard_new("caret")
val (_after, answer) = cs_handle_command(d, "/max")
expect(answer).to_contain("no agent selected")
```

</details>

### cs dashboard - the command line

#### never silently drops a chat message I typed with nothing selected

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: cs-dashboard-command-line (expected show, folded, detail, or skip)


- type bare text into an empty dashboard
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: after.log.len() equals `0)  # oracle: an undeliverable message must not enter the log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-008
step("type bare text into an empty dashboard")
val d = cs_dashboard_new("caret")
val (after, answer) = cs_handle_command(d, "please summarize the plan")
expect(after.log.len()).to_equal(0)  # oracle: an undeliverable message must not enter the log
expect(answer).to_contain("no agent selected")
```

</details>

#### routes bare text to the selected agent

- type bare text with one agent selected
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: after.log.len() equals `2)  # oracle: the log records the echoed input plus the chat action`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-008
step("type bare text with one agent selected")
val d = _launched("caret", ["claude"])
val (after, answer) = cs_handle_command(d, "please summarize the plan")
expect(answer).to_contain("chat:a1")
expect(answer).to_contain("summarize")
expect(after.log.len()).to_equal(2)  # oracle: the log records the echoed input plus the chat action
```

</details>

#### names an unknown slash command instead of guessing

- issue a slash command that does not exist
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-009
step("issue a slash command that does not exist")
val d = cs_dashboard_new("caret")
val (_after, answer) = cs_handle_command(d, "/frobnicate")
expect(answer).to_contain("unknown command")
expect(answer).to_contain("/help")
```

</details>

#### offers a short usage list covering every command

- render the help text and check every command is listed
   - Text capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-009
step("render the help text and check every command is listed")
val help = cs_help_text()
expect(help).to_contain("/launch")
expect(help).to_contain("/switch")
expect(help).to_contain("/max")
expect(help).to_contain("/kill")
expect(help).to_contain("/agents")
expect(help).to_contain("/quit")
```

</details>

### cs dashboard - the rendered screen

#### shows status, the roster, the selected agent's detail, and the input last

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: cs-dashboard-render (expected show, folded, detail, or skip)


- build a two-agent dashboard with the second selected
   - TUI capture: after_step
- render at 80x14
- the screen occupies exactly the rows it was given
   - Expected: lines.len() equals `14)  # oracle: the frame fills the requested grid height exactly`
- the first row is the status header
- both agents are listed
- the SELECTED agent's detail is shown
- the input line is the LAST row


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-010
step("build a two-agent dashboard with the second selected")
val base = _launched("caret", ["claude", "codex"])
val a1 = CsAgent(agent_id: "a1", spec: "claude", status: "running",
    pid: 111, pane_id: "%1", cpu_pct: 3.5, rss_mb: 42,
    detail: "pane %1 title a1")
val a2 = CsAgent(agent_id: "a2", spec: "codex", status: "running",
    pid: 222, pane_id: "%2", cpu_pct: 1.5, rss_mb: 21,
    detail: "pane %2 title a2")
val d = CsDashboard(session: "caret",
    manager_status: "connected: tmux session caret, 2 agent(s), 2 running",
    agents: [a1, a2], selected: 1, input: "hello there", log: [], screen: [])

step("render at 80x14")
val out = cs_render(d, 80, 14)
val lines = _lines(out)

step("the screen occupies exactly the rows it was given")
expect(lines.len()).to_equal(14)  # oracle: the frame fills the requested grid height exactly

step("the first row is the status header")
expect(lines[0]).to_contain("caret")
expect(lines[0]).to_contain("connected")
expect(lines[0]).to_contain("2 running")

step("both agents are listed")
expect(out).to_contain("a1")
expect(out).to_contain("a2")

step("the SELECTED agent's detail is shown")
expect(out).to_contain("DETAIL")
expect(out).to_contain("%2")
expect(out).to_contain("21")

step("the input line is the LAST row")
expect(lines[13]).to_contain("hello there")
assert_false(lines[12].contains("hello there"))
```

</details>

#### keeps the input on the bottom row even when the roster is long

- build a roster longer than the screen can list
   - TUI capture: after_step
- render into fewer rows than the roster needs
   - Expected: lines.len() equals `8)  # oracle: the frame must never exceed the requested grid height`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-011
step("build a roster longer than the screen can list")
var agents: [CsAgent] = []
var i = 0
while i < 12:
    agents = agents + [CsAgent(agent_id: "a" + (i + 1).to_text(),
        spec: "claude", status: "running", pid: 100 + i,
        pane_id: "%" + (i + 1).to_text(), cpu_pct: 1.0, rss_mb: 10,
        detail: "d")]
    i = i + 1
val d = CsDashboard(session: "caret", manager_status: "connected: tmux",
    agents: agents, selected: 0, input: "tail", log: [], screen: [])

step("render into fewer rows than the roster needs")
val lines = _lines(cs_render(d, 60, 8))
expect(lines.len()).to_equal(8)  # oracle: the frame must never exceed the requested grid height
expect(lines[7]).to_contain("tail")
```

</details>

#### shows the dashboard on the left and the selected agent's screen on the right

- Select an agent whose pane has printed three lines
   - TUI capture: after_step
- Render a 100x12 frame
   - Expected: lines.len() equals `12)  # oracle: the frame fills the requested grid height exactly`
- The status header and the input line span the full width
- Every middle row is split at the same column: dashboard | screen
   - Expected: lines[row].index_of("|") equals `bar`
- The left half lists agents, the right half names the selected agent
- The agent's newest output is on the right, below its title


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-014
step("Select an agent whose pane has printed three lines")
val a1 = CsAgent(agent_id: "a1", spec: "claude", status: "running",
    pid: 111, pane_id: "id3", cpu_pct: 1.0, rss_mb: 10, detail: "one")
val a2 = CsAgent(agent_id: "a2", spec: "codex", status: "running",
    pid: 222, pane_id: "id4", cpu_pct: 2.0, rss_mb: 20, detail: "two")
val d = CsDashboard(session: "caret", manager_status: "connected: smux",
    agents: [a1, a2], selected: 1, input: "draft",
    log: [], screen: ["old line", "codex> thinking", "codex> hello from a2"])

step("Render a 100x12 frame")
val lines = _lines(cs_render(d, 100, 12))
expect(lines.len()).to_equal(12)  # oracle: the frame fills the requested grid height exactly

step("The status header and the input line span the full width")
expect(lines[0]).to_contain("connected: smux")
expect(lines[11]).to_contain("draft")

step("Every middle row is split at the same column: dashboard | screen")
val bar = lines[1].index_of("|")
expect(bar).to_be_greater_than(30)
var row = 1
while row < 11:
    expect(lines[row].index_of("|")).to_equal(bar)
    row = row + 1

step("The left half lists agents, the right half names the selected agent")
expect(lines[1].substring(0, bar)).to_contain("AGENTS")
expect(lines[1].substring(bar, lines[1].len())).to_contain("AGENT  a2")

step("The agent's newest output is on the right, below its title")
var found = false
for line in lines:
    val bi = line.index_of("|")
    if bi > 0 and line.substring(bi, line.len()).contains("hello from a2"):
        found = true
assert_true(found)
```

</details>

#### falls back to one column when the terminal is too narrow to split

- Render the same dashboard into a 50-column terminal
   - TUI capture: after_step
- No split column below the header, and the agent screen is not squeezed in
   - Expected: lines[row] does not contain `|`
   - Expected: out does not contain `agent says hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-014
step("Render the same dashboard into a 50-column terminal")
val a1 = CsAgent(agent_id: "a1", spec: "claude", status: "running",
    pid: 111, pane_id: "id3", cpu_pct: 1.0, rss_mb: 10, detail: "one")
val d = CsDashboard(session: "caret", manager_status: "connected: smux",
    agents: [a1], selected: 0, input: "x", log: [], screen: ["agent says hi"])
val out = cs_render(d, 50, 8)
step("No split column below the header, and the agent screen is not squeezed in")
val lines = _lines(out)
var row = 1
while row < lines.len():
    expect(lines[row].contains("|")).to_equal(false)
    row = row + 1
expect(out.contains("agent says hi")).to_equal(false)
```

</details>

#### says it has not polled yet rather than showing an empty screen as truth

- render a dashboard that has never been polled
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-012
step("render a dashboard that has never been polled")
val fresh = cs_dashboard_new("caret")
expect(fresh.manager_status).to_contain("unknown")
expect(cs_render(fresh, 80, 6)).to_contain("unknown")
```

</details>

### cs dashboard - honest state when nothing can be measured

#### reports an honest manager status and no fabricated usage after a poll

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: cs-dashboard-honest-state (expected show, folded, detail, or skip)


- launch an agent that was never really started, then poll
   - TUI capture: after_step
- the status names a real outcome, not the un-polled placeholder
- an unlaunched agent still reports no measurement, not zero
   - Expected: polled.agents.len() equals `1)  # oracle: the launched spec stays on the roster even when unreachable`
   - Expected: polled.agents[0].rss_mb equals `-1)  # oracle: -1 means never measured, never zero`
- the rendered screen shows dashes where nothing was measured


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-013
step("launch an agent that was never really started, then poll")
val d = _launched("cs-dashboard-spec-no-such-session", ["claude"])
val polled = cs_refresh(d)

step("the status names a real outcome, not the un-polled placeholder")
assert_false(polled.manager_status.contains("not polled"))
val reachable = polled.manager_status.starts_with("connected")
val unreachable = polled.manager_status.starts_with("disconnected")
assert_true(reachable or unreachable)

step("an unlaunched agent still reports no measurement, not zero")
expect(polled.agents.len()).to_equal(1)  # oracle: the launched spec stays on the roster even when unreachable
expect(polled.agents[0].rss_mb).to_equal(-1)  # oracle: -1 means never measured, never zero
assert_false(polled.agents[0].status == "running")

step("the rendered screen shows dashes where nothing was measured")
expect(cs_render(polled, 80, 12)).to_contain("cpu -")
```

</details>

#### refuses to pretend a message was delivered when it cannot be

- send a message to an agent whose pane cannot exist
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CSDASH-013
step("send a message to an agent whose pane cannot exist")
val d = _launched("cs-dashboard-spec-no-such-session", ["claude"])
val (_after, action) = cs_handle_command(d, "ping")
val (_after2, result) = cs_apply_action(d, action)
expect(result).to_contain("cannot deliver")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
