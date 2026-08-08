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
- REQ-LLM-CARET-CLI-HARDEN-006: Shipped CLI/provider, session, permission,
  retry, parsing, and hidden-command behavior must have modern SSpec scenarios
  that import and exercise production declarations rather than copied test
  implementations.
- REQ-LLM-CARET-TUI-HARDEN-007: The interactive loop must select TUI versus
  plain mode deterministically, fail before alternate-screen mutation when raw
  mode is unavailable, and restore cursor, alternate-screen, and raw-mode state
  after every modeled exit.
- REQ-LLM-CARET-HIDDEN-008: Hidden commands must remain undisclosed and
  rejected by default, execute only after explicit enablement, and remain
  rejected when their command metadata is disabled.
- REQ-LLM-CARET-TUI-HARDEN-009: TUI frame sizing, raw byte input, UTF-8
  editing, paging, slash dispatch, model submission, persistence, EOF, and
  exit behavior must be testable through an injected production I/O boundary
  and covered without a paid provider.
