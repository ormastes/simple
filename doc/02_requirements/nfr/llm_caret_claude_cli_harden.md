# LLM Caret Claude CLI Harden - NFR Requirements

Date: 2026-07-05

- NFR-LLM-CARET-TRACE-001: The default gate must not require live Claude
  credentials, network access, GPUs, or external model downloads.
- NFR-LLM-CARET-TRACE-002: The checker must finish with ordinary shell/file
  operations and report an explicit `STATUS: PASS` or `STATUS: FAIL`.
- NFR-LLM-CARET-TRACE-003: The trace report must preserve MDSOC+ ownership:
  app-layer provider logic in `src/app/llm_caret`, runtime I/O behind owner
  facades where available, and no broad UI/remote-control migration in this
  lane.
- NFR-LLM-CARET-TRACE-004: The trace gate must be deterministic and derived
  from the current filesystem, not from hardcoded file counts.
- NFR-LLM-CARET-TUI-005: Component tests must not declare app-private runtime
  externs or duplicate the TUI loop; terminal dependencies are supplied through
  the shipped `CaretIo` capability boundary.
- NFR-LLM-CARET-TUI-006: Live-terminal evidence must use a cached compiled
  Caret artifact and a real pseudo-terminal, fail closed when prerequisites are
  absent, emit no paid-provider traffic, and retain artifacts under
  `build/test-artifacts`.
- NFR-LLM-CARET-TUI-007: A frame render must use one terminal-size snapshot,
  and modeled teardown must remain bounded with no retry or polling loop.
