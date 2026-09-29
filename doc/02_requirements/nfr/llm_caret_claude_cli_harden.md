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
