# LLM Caret Claude CLI Harden - Feature Requirements

Date: 2026-07-05

- REQ-LLM-CARET-CLAUDE-TRACE-001: The lane must extract Claude CLI feature
  groups from `tmp/claude/claude-code-main/src` and record their Simple
  `src/app/llm_caret` targets.
- REQ-LLM-CARET-CLAUDE-TRACE-002: Every `src/app/llm_caret/*.spl` file must
  have a mapping row to Claude source or an explicit Simple-only role.
- REQ-LLM-CARET-CLAUDE-TRACE-003: A checker must compute mapped file and LOC
  coverage from the current tree and fail if either coverage value is below
  80%.
- REQ-LLM-CARET-CLAUDE-TRACE-004: A system SSpec must run the checker and
  validate the trace report contract.
- REQ-LLM-CARET-CLAUDE-TRACE-005: The checker must verify that every current
  `fn`, `struct`, and `extern fn` symbol in `src/app/llm_caret/*.spl` appears
  in the Simple symbol trace table.
