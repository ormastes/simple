# LLM Caret Embedded Tmux - System Test Plan

Date: 2026-07-01

## Scope

The system spec verifies the TUI-visible embedded tmux surface for LLM Caret
agent teams. It covers separate process panes, PID/status display, CPU percent,
memory MB, and the empty-team idle pane.

Excluded: live PTY, host tmux, direct process sampling, keyboard routing, and
full tmux keymap parity.

## Execution

```bash
bin/release/simple test test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl --mode=interpreter
bin/release/simple spipe-docgen test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl --output doc/06_spec --no-index
```

## Traceability

| REQ | Description | Test File | Test Cases | Coverage |
|---|---|---|---|---|
| REQ-001 | Reuse Simple tmux model | `test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl` | 1 | Full |
| REQ-002 | Separate process panes | same | 1 | Full |
| REQ-003 | PID/status/CPU/memory TUI | same | 1 | Full |
| REQ-004 | Caller-supplied usage snapshots | same | 1 | Full |
| REQ-005 | Executable SSpec coverage | same | 2 | Full |
| NFR-003 | Empty team idle pane | same | 1 | Full |

Generated manual: `doc/06_spec/test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.md`.
