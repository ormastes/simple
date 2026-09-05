# LLM Caret Embedded Tmux - Architecture

Date: 2026-07-01

## Layers

| Layer | Path | Role |
|---|---|---|
| Existing tmux model | `src/lib/common/tmux_session_model.spl` | session/window/pane model |
| Existing process model | `src/app/llm_caret/agent_runtime.spl` | agent process/team state |
| Embedded view | `src/app/llm_caret/agent_tmux.spl` | pure tmux embedding and TUI rendering |
| System spec | `test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl` | visible TUI evidence |

## Boundary

`agent_tmux.spl` is pure. It consumes `AgentTeamProcess` and caller-supplied
`AgentProcessUsage` snapshots. Process sampling remains outside this module and
can use the existing process-monitor facades when a live caller needs real CPU
and memory data.

## Public API

- `AgentProcessUsage`
- `AgentTmuxEmbed`
- `build_agent_tmux_embed(team, usages) -> AgentTmuxEmbed`
- `render_agent_tmux_tui(embed, team) -> text`
