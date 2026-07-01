# LLM Caret Agent Teams - MDSOC Architecture

Date: 2026-07-01

## Current State

`src/app/llm_caret` has provider wrappers and chat state, but no shared agent/team request node. Tests prefer pure builders with no live CLI dependency.

## To-Be Layers

| Layer | Path | Visibility |
|---|---|---|
| Common request node | `src/app/llm_caret/agent_plan.spl` | public to LLM Caret callers |
| Runtime launcher | `src/app/llm_caret/agent_runtime.spl` | public wrapper over process facade |
| Provider wrappers | `src/app/llm_caret/*_cli.spl` | sibling consumers of prompt/argv outputs |
| CLI/app callers | future `src/app/**` | consume only exported planner APIs |

## Encapsulation

- `agent_plan.spl` owns agent/team/review/advisor/goal request structs and deterministic prompt construction.
- `AgentCapabilitySet` owns the SPipe-like explicit agent, skill, MCP server, and plugin handoff lists.
- `track_agent_file_changes` compares caller-supplied before/after fingerprints by agent.
- `agent_runtime.spl` spawns only already-built single-agent plans and rejects synthetic team plans.
- Provider wrappers do not read agent markdown or track files; they only receive prompt/argv from callers.
- File diff capture and live process supervision remain outside this node.

<!-- sdn-diagram:id=llm-caret-agent-plan -->
```sdn
component "Caller" -> "agent_plan.spl" : request fields
component "agent_plan.spl" -> "Claude/Codex/OpenCode wrapper" : prompt + argv
component "Review caller" -> "agent_plan.spl" : changed files + guidance
```

## Public API

- `AgentLaunchRequest`, `AgentLaunchPlan`, `AgentReviewRequest`
- `build_agent_launch_plan(req) -> AgentLaunchPlan`
- `build_agent_capability_launch_plan(req, caps) -> AgentLaunchPlan`
- `build_agent_team_plan(requests, interaction_mode) -> AgentLaunchPlan`
- `build_low_agent_review_plan(req) -> AgentLaunchPlan`
- `build_claude_advisor_plan(topic, context) -> AgentLaunchPlan`
- `build_codex_goal_plan(objective, context) -> AgentLaunchPlan`
- `launch_agent_plan(agent_id, plan, claude_path, codex_path, opencode_path) -> AgentProcess`

## Matrix

| Raw layer | common request node | public to parent | public to next-layer sibling |
|---|---|---|---|
| LLM Caret planner | `AgentLaunchPlan` | exported structs/functions | prompt/argv only |
| Capability handoff | `AgentCapabilitySet` | explicit agents/skills/MCP/plugins | no discovery or install |
| Runtime launcher | `AgentProcess` | PID/status wrapper | no registry or supervisor |
| Provider wrappers | prompt/argv | no private planner state | no direct file tracking |
