# LLM Caret Embedded Tmux - Domain Research

Date: 2026-07-01

Terminal multiplexers group long-running processes into sessions, windows, and
panes. For an LLM agent dashboard, the useful base contract is not full tmux
parity; it is visible separation of per-agent processes plus process resource
readouts.

## Chosen Slice

- Session: one LLM Caret team.
- Pane: one agent process.
- Process usage: caller-provided CPU percent and memory MB snapshot.
- TUI: deterministic text table for SPipe evidence and operator inspection.

## Deferred

- Live PTY attachment.
- Host tmux dependency.
- Full tmux keymap, copy-mode, mouse, config, or control-mode parity.
- Direct process sampling in the UI module.
