# LLM Caret Agent Teams - MDSOC Architecture

Date: 2026-07-01

## Current State

`src/app/llm_caret` has provider wrappers and chat state, but no shared agent/team request node. Tests prefer pure builders with no live CLI dependency.

## To-Be Layers

| Layer | Path | Visibility |
|---|---|---|
| Common request node | `src/app/llm_caret/agent_plan.spl` | public to LLM Caret callers |
| Provider wrappers | `src/app/llm_caret/*_cli.spl` | sibling consumers of prompt/argv outputs |
| CLI/app callers | future `src/app/**` | consume only exported planner APIs |

## Encapsulation

- `agent_plan.spl` owns agent/team/review/advisor/goal request structs and deterministic prompt construction.
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
- `build_agent_team_plan(requests, interaction_mode) -> AgentLaunchPlan`
- `build_low_agent_review_plan(req) -> AgentLaunchPlan`
- `build_claude_advisor_plan(topic, context) -> AgentLaunchPlan`
- `build_codex_goal_plan(objective, context) -> AgentLaunchPlan`

## Matrix

| Raw layer | common request node | public to parent | public to next-layer sibling |
|---|---|---|---|
| LLM Caret planner | `AgentLaunchPlan` | exported structs/functions | prompt/argv only |
| Provider wrappers | prompt/argv | no private planner state | no direct file tracking |
