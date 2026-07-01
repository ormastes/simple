# Agent Plan Specification

> <details>

<!-- sdn-diagram:id=agent_plan_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agent_plan_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agent_plan_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agent_plan_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Agent Plan Specification

## Scenarios

### LLM Caret agent plans

#### builds a single agent launch plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = AgentLaunchRequest(provider: "", agent_md_path: ".claude/agents/spipe/dev.md", skill_path: ".codex/skills/sp_dev/SKILL.md", task_desc: "implement slice", model: "sonnet", session_id: "s1", extra_args: ["--max-turns", "3"])
val plan = build_agent_launch_plan(req)
expect(plan.provider).to_equal("claude_cli")
expect(plan.mode).to_equal("agent")
expect(plan.prompt).to_contain("Agent: .claude/agents/spipe/dev.md")
expect(plan.prompt).to_contain("Skill: .codex/skills/sp_dev/SKILL.md")
expect(plan.prompt).to_contain("Task: implement slice")
expect(contains(plan.argv, "--model")).to_equal(true)
expect(contains(plan.argv, "--resume")).to_equal(true)
expect(contains(plan.argv, "--max-turns")).to_equal(true)
```

</details>

#### builds a team plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = AgentLaunchRequest(provider: "claude_cli", agent_md_path: "agent-a.md", skill_path: "skill-a.md", task_desc: "research", model: "", session_id: "", extra_args: [])
val b = AgentLaunchRequest(provider: "codex", agent_md_path: "agent-b.md", skill_path: "skill-b.md", task_desc: "review", model: "", session_id: "", extra_args: [])
val plan = build_agent_team_plan([a, b], "btw-side")
expect(plan.mode).to_equal("team")
expect(plan.prompt).to_contain("Team interaction: btw-side")
expect(plan.prompt).to_contain("Member 2")
expect(plan.summary).to_equal("team:2")
```

</details>

#### builds a low agent review plan with tracked files

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = AgentReviewRequest(reviewer: "normal", changed_files: ["src/a.spl", "doc/b.md"], guidance: "review file changes")
val plan = build_low_agent_review_plan(req)
expect(plan.mode).to_equal("review")
expect(plan.prompt).to_contain("- src/a.spl")
expect(plan.prompt).to_contain("- doc/b.md")
expect(plan.summary).to_equal("review:2")
```

</details>

#### builds a per-agent change review plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = AgentFileChangeSet(agent_id: "spark", changed_files: ["src/a.spl"])
val b = AgentFileChangeSet(agent_id: "haiku", changed_files: ["doc/b.md", "test/c.spl"])
val plan = build_agent_change_review_plan([a, b], "review each agent")
expect(plan.mode).to_equal("agent_change_review")
expect(plan.prompt).to_contain("Agent: spark")
expect(plan.prompt).to_contain("Agent: haiku")
expect(plan.summary).to_equal("agent-change-review:3")
```

</details>

#### builds a claude advisor plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = build_claude_advisor_plan("architecture", "compare options")
expect(plan.provider).to_equal("claude_cli")
expect(plan.mode).to_equal("advisor")
expect(plan.prompt).to_contain("Advisor topic: architecture")
```

</details>

#### builds a codex goal plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = build_codex_goal_plan("finish feature", "preserve scope")
expect(plan.provider).to_equal("codex")
expect(plan.mode).to_equal("goal")
expect(plan.argv[0]).to_equal("exec")
expect(plan.prompt).to_contain("Goal: finish feature")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/agent_plan_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM Caret agent plans

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
