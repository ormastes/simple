# Agent Team

Create and orchestrate multi-agent teams via MCP tools. Teams coordinate multiple agent roles working on a shared task.

## Quick Start

1. **Create team:** Call `agent_team_create` with name, agents list, coordination strategy
2. **Run prompt:** Call `agent_team_run` with team_id and prompt
3. **Execute:** Follow the instruction returned for the current agent
4. **Continue:** Call `agent_team_run` again for the next agent's turn

## MCP Tools

| Tool | Purpose |
|------|---------|
| `agent_team_create` | Create team with agents and coordination strategy |
| `agent_team_run` | Get next agent instruction for a prompt |

## Parameters

### agent_team_create
- `name` (required) — Team name
- `agents` (required) — Comma-separated agent names (e.g., "coder,reviewer,tester")
- `coordination` — Strategy: `sequential` (default), `parallel`, `round_robin`

### agent_team_run
- `team_id` (required) — Team to run
- `prompt` (required) — Task for the team

## Coordination Strategies

| Strategy | Behavior |
|----------|----------|
| `sequential` | Agents execute in order, one at a time. Each step advances to next agent. |
| `parallel` | All agents receive the same prompt simultaneously. |
| `round_robin` | Cycles through agents, wrapping around after the last. |

## State

State files stored in `.build/agent_loop/teams/{id}.state`

## Example Flow

```
You: Create a code review team
AI: [calls agent_team_create(name: "review", agents: "coder,reviewer,tester", coordination: "sequential")]
AI: [calls agent_team_run(team_id: "team_123", prompt: "Implement and review feature X")]
→ Returns instruction for "coder" agent (step 1/3)
AI: [implements feature as coder]
AI: [calls agent_team_run(team_id: "team_123", prompt: "Review the implementation")]
→ Returns instruction for "reviewer" agent (step 2/3)
AI: [reviews as reviewer]
AI: [calls agent_team_run(team_id: "team_123", prompt: "Write tests")]
→ Returns instruction for "tester" agent (step 3/3)
```

## Combining with Agent Loop

Teams work well with agent loops. Start a loop, and within each iteration use a team to coordinate multiple agents:

```
agent_loop_start(prompt: "Iteratively improve code quality")
  → agent_team_run(team_id, prompt: "Fix issues found")
  → agent_loop_step(loop_id, result: "3 issues fixed")
  → repeat...
```
