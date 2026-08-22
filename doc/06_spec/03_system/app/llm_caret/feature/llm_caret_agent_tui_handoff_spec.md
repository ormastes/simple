# LLM Caret Agent TUI Handoff

> Verifies the llm caret agent tui handoff behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Agent TUI Handoff

Verifies the llm caret agent tui handoff behaviour end to end so maintainers of this

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
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llm caret agent tui handoff behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

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

- Verify: should render agent skill MCP and plugin capabilities
- Build a SPipe-style agent capability launch plan
- Render the operator TUI handoff


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-011 REQ-007 REQ-012
step("Verify: should render agent skill MCP and plugin capabilities")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should render btw and side mailbox messages
- Post visible team messages
- Render the team mailbox TUI


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-011 REQ-007 REQ-012
step("Verify: should render btw and side mailbox messages")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should render an agent inbox view
- Filter team messages for one agent
- Render the agent-specific TUI


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-011 REQ-007 REQ-012
step("Verify: should render an agent inbox view")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- **Requirements:** `doc/02_requirements/feature/llm_caret_agent_teams.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_agent_teams.md`
- **Design:** `doc/05_design/app/tools/llm_caret_agent_teams.md`
- **Research:** `doc/01_research/local/llm_caret_agent_teams.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d8fa7395b5243a6f5b32c3b6699f7462f4629a5369370bbff457d66aeaefcc17`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d8fa7395b5243a6f5b32c3b6699f7462f4629a5369370bbff457d66aeaefcc17`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d8fa7395b5243a6f5b32c3b6699f7462f4629a5369370bbff457d66aeaefcc17`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl:146:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render agent skill MCP and plugin capabilities' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl:164:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render btw and side mailbox messages' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl:179:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render an agent inbox view' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
