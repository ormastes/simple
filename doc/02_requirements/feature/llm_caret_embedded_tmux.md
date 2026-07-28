# LLM Caret Embedded Tmux - Feature Requirements

Date: 2026-07-01

- REQ-001: Reuse the existing Simple tmux session/pane model for embedded LLM Caret process views.
- REQ-002: Represent separate agent processes as separate embedded tmux panes.
- REQ-003: Show per-process PID, status, CPU percent, and memory MB in a TUI-readable view.
- REQ-004: Keep process CPU/memory snapshots caller-supplied so the feature module does not add direct runtime or shell sampling.
- REQ-005: Provide executable SSpec coverage for the embedded tmux TUI.
