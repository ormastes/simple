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
| 15 | 15 | 0 | 0 |

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

#### builds agent skill mcp plugin capability prompt

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = AgentLaunchRequest(provider: "claude_cli", agent_md_path: ".claude/agents/spipe/dev.md", skill_path: ".codex/skills/sp_dev/SKILL.md", task_desc: "plan agents", model: "", session_id: "", extra_args: [])
val caps = AgentCapabilitySet(agent_paths: [".claude/agents/spipe/dev.md"], skill_paths: [".codex/skills/sp_dev/SKILL.md"], mcp_servers: ["simple-mcp"], plugins: ["ponytail"])
val plan = build_agent_capability_launch_plan(req, caps)
expect(plan.mode).to_equal("agent_capabilities")
expect(plan.prompt).to_contain("Agents:")
expect(plan.prompt).to_contain("- simple-mcp")
expect(plan.prompt).to_contain("- ponytail")
expect(plan.summary).to_equal("agent-capabilities:1:1:1:1")
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

#### builds btw side team interaction transcript

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btw = AgentTeamMessage(from_agent: "lead", to_agent: "spark", channel: "btw", body: "check docs")
val side = AgentTeamMessage(from_agent: "spark", to_agent: "lead", channel: "side", body: "docs updated")
val plan = build_btw_side_interaction_plan([btw, side])
expect(plan.mode).to_equal("team_interaction")
expect(plan.prompt).to_contain("btw: lead -> spark")
expect(plan.prompt).to_contain("side: spark -> lead")
expect(plan.summary).to_equal("team-interaction:btw-side:2")
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

#### tracks changed files by agent fingerprint

- AgentFileFingerprint
- AgentFileFingerprint
- AgentFileFingerprint
- AgentFileFingerprint
   - Expected: changes.len() equals `2`
   - Expected: changes[0].agent_id equals `spark`
   - Expected: changes[0].changed_files.len() equals `2`
   - Expected: changes[1].agent_id equals `haiku`
   - Expected: changes[1].changed_files[0] equals `doc/old.md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = [
    AgentFileFingerprint(agent_id: "spark", path: "src/a.spl", fingerprint: "1"),
    AgentFileFingerprint(agent_id: "haiku", path: "doc/old.md", fingerprint: "1")
]
val after = [
    AgentFileFingerprint(agent_id: "spark", path: "src/a.spl", fingerprint: "2"),
    AgentFileFingerprint(agent_id: "spark", path: "test/new.spl", fingerprint: "1")
]
val changes = track_agent_file_changes(before, after)
expect(changes.len()).to_equal(2)
expect(changes[0].agent_id).to_equal("spark")
expect(changes[0].changed_files.len()).to_equal(2)
expect(changes[1].agent_id).to_equal("haiku")
expect(changes[1].changed_files[0]).to_equal("doc/old.md")
```

</details>

#### snapshots existing agent files only

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = snapshot_agent_files_from_existing("spark", ["src/a.spl", "", "missing.spl", "doc/b.md"], ["src/a.spl", "doc/b.md"], ["sha-a", "sha-b"])
expect(snap.len()).to_equal(2)
expect(snap[0].agent_id).to_equal("spark")
expect(snap[0].fingerprint).to_equal("sha-a")
expect(snap[1].path).to_equal("doc/b.md")
```

</details>

#### parses vcs changed files for an agent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val changes = parse_vcs_changed_files("spark", "src/a.spl\n\n doc/b.md \nsrc/a.spl\n")
expect(changes.agent_id).to_equal("spark")
expect(changes.changed_files.len()).to_equal(2)
expect(changes.changed_files[0]).to_equal("src/a.spl")
expect(changes.changed_files[1]).to_equal("doc/b.md")
```

</details>

#### discovers mcp and plugin names from manifests

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcp_json = "{\"name\":\"io.github.simple-mcp\",\"packages\":[{\"identifier\":\"@simple-lang/mcp-server\"}]},"
val plugin_sdn = "plugin:\n  name: spipe\n  mcp: mcp/server.js\n"
val mcp = parse_mcp_manifest(mcp_json)
val plugins = parse_plugin_manifest(plugin_sdn)
expect(mcp.len()).to_equal(2)
expect(mcp[0]).to_equal("io.github.simple-mcp")
expect(mcp[1]).to_equal("@simple-lang/mcp-server")
expect(plugins[0]).to_equal("spipe")
```

</details>

#### builds plugin install args

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_plugin_install_args("ponytail", "", ["--local"])
expect(args[0]).to_equal("install-plugin")
expect(args[1]).to_equal("ponytail")
expect(args[2]).to_equal("--local")
```

</details>

#### resolves provider commands for launch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(agent_command_for_provider("codex", "", "", "")).to_equal("codex")
expect(agent_command_for_provider("claude_cli", "claude-dev", "", "")).to_equal("claude-dev")
expect(agent_command_for_provider("opencode_cli", "", "", "opencode-dev")).to_equal("opencode-dev")
```

</details>

#### summarizes team process launch state

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = AgentProcess(agent_id: "a", status: "started", reason: "process_spawned", pid: 10)
val b = AgentProcess(agent_id: "b", status: "error", reason: "spawn_failed", pid: -1)
val team = summarize_agent_team("team-1", [a, b])
expect(team.status).to_equal("partial")
expect(team.reason).to_equal("started:1/2")
expect(team.processes.len()).to_equal(2)
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
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
