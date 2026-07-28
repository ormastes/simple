# LLM Caret Embedded Tmux

Date: 2026-07-01

Use `src/app/llm_caret/agent_tmux.spl` to render agent-team processes as an
embedded tmux-style TUI.

Supported:

- one tmux pane row per `AgentProcess`
- PID and process status
- caller-supplied CPU percent
- caller-supplied memory MB
- explicit idle pane for empty teams

Not supported in this slice:

- host tmux execution
- live PTY attach
- direct `/proc` or shell sampling inside LLM Caret
- keyboard/control-mode parity

Default verification:

```bash
bin/release/simple test test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl --mode=interpreter
bin/release/simple check src/app/llm_caret/agent_tmux.spl
```
