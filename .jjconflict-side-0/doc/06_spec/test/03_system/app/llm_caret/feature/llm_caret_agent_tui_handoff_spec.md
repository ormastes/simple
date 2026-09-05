# LLM Caret Agent TUI Handoff

> Proves the LLM Caret agent surface has a TUI-readable handoff for SPipe-style agent, skill, MCP, and plugin capabilities, plus visible `btw` and `side` team messages.

<!-- sdn-diagram:id=llm_caret_agent_tui_handoff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_caret_agent_tui_handoff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_caret_agent_tui_handoff_spec -> std
llm_caret_agent_tui_handoff_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_caret_agent_tui_handoff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Agent TUI Handoff

Proves the LLM Caret agent surface has a TUI-readable handoff for SPipe-style agent, skill, MCP, and plugin capabilities, plus visible `btw` and `side` team messages.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/llm_caret_agent_teams.md |
| Plan | doc/03_plan/sys_test/llm_caret_agent_teams.md |
| Design | doc/05_design/app/tools/llm_caret_agent_teams.md |
| Research | doc/01_research/local/llm_caret_agent_teams.md |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves the LLM Caret agent surface has a TUI-readable handoff for SPipe-style
agent, skill, MCP, and plugin capabilities, plus visible `btw` and `side` team
messages.

**Requirements:** doc/02_requirements/feature/llm_caret_agent_teams.md
**Plan:** doc/03_plan/sys_test/llm_caret_agent_teams.md
**Design:** doc/05_design/app/tools/llm_caret_agent_teams.md
**Research:** doc/01_research/local/llm_caret_agent_teams.md
**Guide:** doc/07_guide/app/llm/llm_caret_agent_teams.md
**TUI Captures:** inline text returned by `render_agent_handoff_tui` and `render_agent_mailbox_tui`

## Syntax

The system surface is pure Simple and does not start Claude, Codex, MCP, or a
plugin installer.

1. Build an `AgentLaunchRequest` with an agent markdown path, skill path, task,
   provider, and optional model/session fields.
2. Build an `AgentCapabilitySet` containing SPipe-style agent, skill, MCP, and
   plugin entries.
3. Call `build_agent_capability_launch_plan` to produce the prompt/argv handoff.
4. Call `render_agent_handoff_tui` to render the operator-facing TUI text.
5. Use `new_agent_team_mailbox`, `post_btw_message`, and `post_side_message`
   for pure team interaction state.
6. Call `render_agent_mailbox_tui` or `render_agent_messages_tui` for visible
   mailbox and inbox views.

## Examples

Capability handoff TUI:

```text
LLM Caret Agent Handoff
Mode: agent_capabilities
Summary: agent-capabilities:1:1:1:1
Agents
  - .claude/agents/spipe/dev.md
Skills
  - .codex/skills/sp_dev/SKILL.md
MCP
  - @simple-lang/mcp-server
Plugins
  - spipe
```

Team mailbox TUI:

```text
LLM Caret Team Mailbox
Team: team-spipe
btw: lead -> spark
  review generated manual
side: spark -> lead
  manual is readable
```

## Manual Flow

The first scenario proves the SPipe-compatible handoff appears in a TUI text
surface with all four capability groups visible. The second scenario proves
`btw` and `side` messages render as an ordered team mailbox. The third scenario
proves an individual agent can view its inbox, including broadcast and direct
messages.

## Traceability

| Requirement | Scenario | Evidence |
|---|---|---|
| REQ-006 | render agent skill MCP and plugin capabilities | TUI contains Agents, Skills, MCP, and Plugins sections |
| REQ-011 | render agent skill MCP and plugin capabilities | TUI contains the MCP package and plugin name used by SPipe handoff |
| REQ-007 | render btw and side mailbox messages | TUI contains ordered `btw` and `side` transcript lines |
| REQ-012 | render an agent inbox view | TUI contains broadcast and direct inbox messages for one agent |

## Pass Criteria

- The handoff view shows the agent markdown path.
- The handoff view shows the selected SPipe skill path.
- The handoff view shows the MCP package name.
- The handoff view shows the plugin name.
- The team mailbox view shows both `btw` and `side` channels.
- The inbox view includes broadcast messages addressed to `*`.
- The inbox view includes direct messages addressed to the selected agent.
- No scenario starts an external LLM provider.
- No scenario installs a plugin.
- No scenario queries a network registry.

## Failure Signals

- A capability is present in the data but missing from the TUI text.
- `btw` and `side` channels collapse into unlabeled plain text.
- Broadcast messages disappear from an agent inbox.
- Direct messages for the selected agent disappear from the inbox view.
- A future implementation replaces pure rendering with process execution in
  this spec.

## Operator Notes

This is a base TUI system test. It intentionally treats the rendered text as the
operator contract because LLM Caret callers need a readable handoff before they
launch side agents, ask an advisor, or request review. A later full-screen TUI
can keep the same text sections and add keyboard navigation, persistence, or
live transport behind separate requirements.

## Exclusions

This spec does not execute plugin installs, query a live MCP registry, start a
long-running supervisor, or provide persistent chat transport. Those behaviors
remain separate lanes. This spec only proves the TUI-visible base contract that
callers can use before handing the plan to real provider wrappers.

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| TUI Captures | 1 |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `inline text returned by `render_agent_handoff_tui` and `render_agent_mailbox_tui`` | TUI capture | `inline text returned by `render_agent_handoff_tui` and `render_agent_mailbox_tui`` |

## Scenarios

### LLM Caret agent TUI handoff

### REQ-006 and REQ-011: SPipe-style capabilities

#### should render agent skill MCP and plugin capabilities

- Build a SPipe-style agent capability launch plan
- Render the operator TUI handoff


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a SPipe-style agent capability launch plan")
val req = AgentLaunchRequest(provider: "claude_cli", agent_md_path: ".claude/agents/spipe/dev.md", skill_path: ".codex/skills/sp_dev/SKILL.md", task_desc: "add system coverage", model: "", session_id: "", extra_args: [])
val caps = AgentCapabilitySet(agent_paths: [".claude/agents/spipe/dev.md"], skill_paths: [".codex/skills/sp_dev/SKILL.md"], mcp_servers: ["@simple-lang/mcp-server"], plugins: ["spipe"])
val plan = build_agent_capability_launch_plan(req, caps)
step("Render the operator TUI handoff")
val tui = render_agent_handoff_tui(plan, caps)
expect(tui).to_contain("LLM Caret Agent Handoff")
expect(tui).to_contain("Agents")
expect(tui).to_contain(".claude/agents/spipe/dev.md")
expect(tui).to_contain(".codex/skills/sp_dev/SKILL.md")
expect(tui).to_contain("@simple-lang/mcp-server")
expect(tui).to_contain("spipe")
```

</details>

### REQ-007 and REQ-012: team interaction

#### should render btw and side mailbox messages

- Post visible team messages
- var mailbox = new agent team mailbox
- mailbox = post btw message
- mailbox = post side message
- Render the team mailbox TUI


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Post visible team messages")
var mailbox = new_agent_team_mailbox("team-spipe")
mailbox = post_btw_message(mailbox, "lead", "spark", "review generated manual")
mailbox = post_side_message(mailbox, "spark", "lead", "manual is readable")
step("Render the team mailbox TUI")
val tui = render_agent_mailbox_tui(mailbox)
expect(tui).to_contain("LLM Caret Team Mailbox")
expect(tui).to_contain("btw: lead -> spark")
expect(tui).to_contain("side: spark -> lead")
expect(tui).to_contain("manual is readable")
```

</details>

#### should render an agent inbox view

- Filter team messages for one agent
- var mailbox = new agent team mailbox
- mailbox = post btw message
- mailbox = post side message
- Render the agent-specific TUI


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Filter team messages for one agent")
var mailbox = new_agent_team_mailbox("team-spipe")
mailbox = post_btw_message(mailbox, "lead", "*", "shared handoff")
mailbox = post_side_message(mailbox, "spark", "lead", "private note")
val inbox = agent_team_inbox(mailbox, "lead")
step("Render the agent-specific TUI")
val tui = render_agent_messages_tui(inbox)
expect(tui).to_contain("LLM Caret Agent Messages")
expect(tui).to_contain("shared handoff")
expect(tui).to_contain("private note")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/llm_caret_agent_teams.md](doc/02_requirements/feature/llm_caret_agent_teams.md)
- **Plan:** [doc/03_plan/sys_test/llm_caret_agent_teams.md](doc/03_plan/sys_test/llm_caret_agent_teams.md)
- **Design:** [doc/05_design/app/tools/llm_caret_agent_teams.md](doc/05_design/app/tools/llm_caret_agent_teams.md)
- **Research:** [doc/01_research/local/llm_caret_agent_teams.md](doc/01_research/local/llm_caret_agent_teams.md)


</details>
