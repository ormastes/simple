# LLM Caret Embedded Tmux - NFR Requirements

Date: 2026-07-01

- NFR-001: TUI rendering is deterministic pure text.
- NFR-002: The LLM Caret embedding layer adds no new direct `rt_*`, `/proc`, or shell process-sampling calls.
- NFR-003: Empty teams render an explicit idle pane instead of failing.
- NFR-004: Generated SPipe manual documentation has 0 stubs.
