---
name: agents
description: Agent loop patterns, team orchestration, and skill/command routing for Claude Code
---

# Agents

## Section 1: Agent Loop

Start and manage iterative agent loops via MCP tools. The AI client drives the loop — MCP provides bookkeeping only.

### Quick Start

1. **Start a loop:** Call `agent_loop_start` with a prompt and optional max_iterations
2. **Do work:** Execute the prompt's task
3. **Report result:** Call `agent_loop_step` with the loop_id and your result
4. **Repeat:** If status is "active", continue working on the prompt. If "completed", stop.
5. **Manual stop:** Call `agent_loop_stop` to end early

### MCP Tools

| Tool | Purpose |
|------|---------|
| `agent_loop_start` | Create loop with prompt, max_iterations, completion_condition, agent |
| `agent_loop_status` | Check iteration count, status, last_result |
| `agent_loop_step` | Submit result, get next_prompt or "completed" |
| `agent_loop_stop` | End loop early, get summary |

### Parameters

#### agent_loop_start
- `prompt` (required) — The task to iterate on
- `max_iterations` — Max iterations before auto-complete (default: 10)
- `completion_condition` — String to match in result to auto-complete
- `agent` — Agent name/role for context

#### agent_loop_step
- `loop_id` (required) — Loop to advance
- `result` — Result from current iteration

### Completion Detection

A loop completes when any of:
1. `max_iterations` reached
2. `completion_condition` string found in step result
3. Explicit `agent_loop_stop` call

### State

State files stored in `.build/agent_loop/loops/{id}.state`

### Hook Integration

When a loop is active, the Claude Code stop hook (`scripts/agent-loop-hook.shs`) detects it and prompts continuation. This enables automatic re-prompting when the agent pauses.

### Example Flow

```
You: Start a loop to fix all lint errors
AI: [calls agent_loop_start(prompt: "Fix lint errors", max_iterations: 5, completion_condition: "0 errors")]
AI: [runs linter, fixes errors]
AI: [calls agent_loop_step(loop_id: "loop_123", result: "Fixed 3 errors, 2 remaining")]
AI: [continues fixing...]
AI: [calls agent_loop_step(loop_id: "loop_123", result: "0 errors remaining")]
→ Loop auto-completes because result contains "0 errors"
```

---

## Section 2: Agent Team

Create and orchestrate multi-agent teams via MCP tools. Teams coordinate multiple agent roles working on a shared task.

### Quick Start

1. **Create team:** Call `agent_team_create` with name, agents list, coordination strategy
2. **Run prompt:** Call `agent_team_run` with team_id and prompt
3. **Execute:** Follow the instruction returned for the current agent
4. **Continue:** Call `agent_team_run` again for the next agent's turn

### MCP Tools

| Tool | Purpose |
|------|---------|
| `agent_team_create` | Create team with agents and coordination strategy |
| `agent_team_run` | Get next agent instruction for a prompt |
| `agent_team_status` | Get team status, current agent index, coordination info |
| `agent_team_stop` | Stop team early and get summary |

### Parameters

#### agent_team_create
- `name` (required) — Team name
- `agents` (required) — Comma-separated agent names (e.g., "coder,reviewer,tester")
- `coordination` — Strategy: `sequential` (default), `parallel`, `round_robin`

#### agent_team_run
- `team_id` (required) — Team to run
- `prompt` (required) — Task for the team
- `result` — Result from previous agent (stored and passed to next agent)

#### agent_team_status
- `team_id` (required) — Team ID to check

#### agent_team_stop
- `team_id` (required) — Team ID to stop

### Coordination Strategies

| Strategy | Behavior |
|----------|----------|
| `sequential` | Agents execute in order. Team completes after the last agent finishes. |
| `parallel` | Returns ALL agents' instructions in one response. Team completes immediately. |
| `round_robin` | Cycles through agents, wrapping around after the last. Never auto-completes. |

### State

State files stored in `.build/agent_loop/teams/{id}.state`

### Example Flow (Sequential with Result Passing)

```
You: Create a code review team
AI: [calls agent_team_create(name: "review", agents: "coder,reviewer,tester", coordination: "sequential")]
AI: [calls agent_team_run(team_id: "team_123", prompt: "Implement and review feature X")]
→ Returns instruction for "coder" (step 1/3), status: "active"
AI: [implements feature as coder]
AI: [calls agent_team_run(team_id: "team_123", prompt: "Review the implementation", result: "Added 3 files, 200 lines")]
→ Returns instruction for "reviewer" (step 2/3), includes previous results, status: "active"
AI: [reviews as reviewer]
AI: [calls agent_team_run(team_id: "team_123", prompt: "Write tests", result: "LGTM, minor style nit")]
→ Returns instruction for "tester" (step 3/3), includes all previous results, status: "completed"
AI: [writes tests — team is done]
```

### Example Flow (Parallel)

```
AI: [calls agent_team_create(name: "analysis", agents: "security,performance,style", coordination: "parallel")]
AI: [calls agent_team_run(team_id: "team_456", prompt: "Analyze module X")]
→ Returns ALL agents' instructions at once, status: "completed"
→ AI can dispatch all three analyses simultaneously
```

### Combining with Agent Loop

Teams work well with agent loops. Start a loop, and within each iteration use a team to coordinate multiple agents:

```
agent_loop_start(prompt: "Iteratively improve code quality")
  → agent_team_run(team_id, prompt: "Fix issues found")
  → agent_loop_step(loop_id, result: "3 issues fixed")
  → repeat...
```
