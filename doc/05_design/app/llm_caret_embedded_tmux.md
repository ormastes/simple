# LLM Caret Embedded Tmux - Design

Date: 2026-07-01

## Data

`AgentProcessUsage` stores `agent_id`, `pid`, `cpu_percent`, and `memory_mb`.
`AgentTmuxEmbed` stores the team id, reused `TmuxSession`, and usage snapshots.

## Flow

1. Caller obtains or models an `AgentTeamProcess`.
2. Caller supplies CPU/memory snapshots for those processes.
3. `build_agent_tmux_embed` creates one tmux pane per process using
   `common.tmux_session_model`.
4. `render_agent_tmux_tui` emits a deterministic TUI table with pane, process,
   PID, status, CPU, and memory.

## Error/Empty Behavior

An empty team renders `pane[0] idle` with zero CPU and memory. Missing usage
snapshots render zero CPU and memory for the affected process.

## Verification

`llm_caret_embedded_tmux_tui_spec.spl` covers multi-process and empty-team TUI
output.
