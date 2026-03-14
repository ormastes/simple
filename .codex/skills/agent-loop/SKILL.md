# Agent Loop — Codex Skill

Iterative agent loop and team orchestration via MCP tools.

## Prerequisites

- Simple MCP server running: `bin/simple_mcp_server`
- MCP connection configured in your Codex project

## Available MCP Tools

### Loop Tools
| Tool | Purpose |
|------|---------|
| `agent_loop_start` | Start iteration loop with prompt, max_iterations, completion_condition |
| `agent_loop_status` | Check loop progress |
| `agent_loop_step` | Submit iteration result, get next prompt or "completed" |
| `agent_loop_stop` | End loop early |

### Team Tools
| Tool | Purpose |
|------|---------|
| `agent_team_create` | Create multi-agent team with coordination strategy |
| `agent_team_run` | Get next agent instruction |

## Usage Pattern

1. Call `agent_loop_start` with your task prompt
2. Execute the task
3. Call `agent_loop_step` with your result
4. If status is "active", repeat from step 2
5. If status is "completed", you're done

## External Wrapper

For non-MCP clients, use the bash wrapper:

```bash
scripts/agent-loop-external.shs 5 "Fix all lint errors"
```

This drives the loop externally, checking `.build/agent_loop/` state between iterations.

## Coordination Strategies for Teams

- `sequential` — agents take turns in order
- `parallel` — all agents get same prompt
- `round_robin` — cycles through agents continuously
