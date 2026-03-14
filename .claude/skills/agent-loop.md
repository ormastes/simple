# Agent Loop

Start and manage iterative agent loops via MCP tools. The AI client drives the loop — MCP provides bookkeeping only.

## Quick Start

1. **Start a loop:** Call `agent_loop_start` with a prompt and optional max_iterations
2. **Do work:** Execute the prompt's task
3. **Report result:** Call `agent_loop_step` with the loop_id and your result
4. **Repeat:** If status is "active", continue working on the prompt. If "completed", stop.
5. **Manual stop:** Call `agent_loop_stop` to end early

## MCP Tools

| Tool | Purpose |
|------|---------|
| `agent_loop_start` | Create loop with prompt, max_iterations, completion_condition, agent |
| `agent_loop_status` | Check iteration count, status, last_result |
| `agent_loop_step` | Submit result, get next_prompt or "completed" |
| `agent_loop_stop` | End loop early, get summary |

## Parameters

### agent_loop_start
- `prompt` (required) — The task to iterate on
- `max_iterations` — Max iterations before auto-complete (default: 10)
- `completion_condition` — String to match in result to auto-complete
- `agent` — Agent name/role for context

### agent_loop_step
- `loop_id` (required) — Loop to advance
- `result` — Result from current iteration

## Completion Detection

A loop completes when any of:
1. `max_iterations` reached
2. `completion_condition` string found in step result
3. Explicit `agent_loop_stop` call

## State

State files stored in `.build/agent_loop/loops/{id}.state`

## Hook Integration

When a loop is active, the Claude Code stop hook (`scripts/agent-loop-hook.shs`) detects it and prompts continuation. This enables automatic re-prompting when the agent pauses.

## Example Flow

```
You: Start a loop to fix all lint errors
AI: [calls agent_loop_start(prompt: "Fix lint errors", max_iterations: 5, completion_condition: "0 errors")]
AI: [runs linter, fixes errors]
AI: [calls agent_loop_step(loop_id: "loop_123", result: "Fixed 3 errors, 2 remaining")]
AI: [continues fixing...]
AI: [calls agent_loop_step(loop_id: "loop_123", result: "0 errors remaining")]
→ Loop auto-completes because result contains "0 errors"
```
