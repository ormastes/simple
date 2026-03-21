---
name: agents
description: Agent loop iteration patterns and multi-agent team orchestration via MCP tools
---

# Agents

## Section 1: Agent Loop

Start and manage iterative agent loops via MCP tools. The AI client drives the loop - MCP provides bookkeeping only.

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
- `prompt` (required) - The task to iterate on
- `max_iterations` - Max iterations before auto-complete (default: 10)
- `completion_condition` - String to match in result to auto-complete
- `agent` - Agent name/role for context

#### agent_loop_step
- `loop_id` (required) - Loop to advance
- `result` - Result from current iteration

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
-> Loop auto-completes because result contains "0 errors"
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

### Parameters

#### agent_team_create
- `name` (required) - Team name
- `agents` (required) - Comma-separated agent names (e.g., "coder,reviewer,tester")
- `coordination` - Strategy: `sequential` (default), `parallel`, `round_robin`

#### agent_team_run
- `team_id` (required) - Team to run
- `prompt` (required) - Task for the team

### Coordination Strategies

| Strategy | Behavior |
|----------|----------|
| `sequential` | Agents execute in order, one at a time. Each step advances to next agent. |
| `parallel` | All agents receive the same prompt simultaneously. |
| `round_robin` | Cycles through agents, wrapping around after the last. |

### State

State files stored in `.build/agent_loop/teams/{id}.state`

### Example Flow

```
You: Create a code review team
AI: [calls agent_team_create(name: "review", agents: "coder,reviewer,tester", coordination: "sequential")]
AI: [calls agent_team_run(team_id: "team_123", prompt: "Implement and review feature X")]
-> Returns instruction for "coder" agent (step 1/3)
AI: [implements feature as coder]
AI: [calls agent_team_run(team_id: "team_123", prompt: "Review the implementation")]
-> Returns instruction for "reviewer" agent (step 2/3)
AI: [reviews as reviewer]
AI: [calls agent_team_run(team_id: "team_123", prompt: "Write tests")]
-> Returns instruction for "tester" agent (step 3/3)
```

### Combining with Agent Loop

Teams work well with agent loops. Start a loop, and within each iteration use a team to coordinate multiple agents:

```
agent_loop_start(prompt: "Iteratively improve code quality")
  -> agent_team_run(team_id, prompt: "Fix issues found")
  -> agent_loop_step(loop_id, result: "3 issues fixed")
  -> repeat...
```
