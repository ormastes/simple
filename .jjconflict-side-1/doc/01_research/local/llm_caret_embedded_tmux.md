# LLM Caret Embedded Tmux - Local Research

Date: 2026-07-01

## Existing Code

- `src/lib/common/tmux_session_model.spl` provides the lightweight Simple tmux
  model: sessions, windows, panes, active selection, add-window, split-pane, and
  active-command helpers.
- `src/os/apps/smux/api.spl` provides the native SimpleOS tmux-like service
  shape for session/window/pane operations.
- `src/os/apps/smux/smux_dashboard.spl` provides dashboard rows and pane layout
  views over smux state.
- `src/app/llm_dashboard/gui/terminal_panel.spl` provides host-tmux WebSocket
  terminal panel rendering for the dashboard.
- `src/lib/gc_sync_mut/process_monitor.spl` re-exports process CPU/memory
  monitoring from `std.gc_async_mut.process_monitor`.
- `src/app/llm_caret/agent_runtime.spl` already models separate agent
  processes with `AgentProcess` and `AgentTeamProcess`.

## Reuse Decision

Use `common.tmux_session_model` for the embedded pane model and reuse LLM Caret
`AgentProcess` state. Do not add host tmux, shell, `/proc`, or process-monitor
calls in the LLM Caret feature module. CPU and memory snapshots are supplied by
the caller so process sampling remains owned by existing process-monitor
facades.
