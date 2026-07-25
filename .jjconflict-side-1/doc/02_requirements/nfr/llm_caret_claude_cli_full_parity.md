# LLM Caret Claude CLI Full Parity - NFR Requirements

Date: 2026-07-05

- NFR-LLM-CARET-FULL-001: Implementation must follow MDSOC+ boundaries:
  Claude parity code lives under `src/app/llm_caret/claude_full`, and shared
  runtime, filesystem, process, HTTP, cryptography, terminal, and UI concerns
  use owner-module facades instead of local runtime shortcuts.
- NFR-LLM-CARET-FULL-002: Default verification must be deterministic and
  offline. Live OAuth, remote-control, browser, and network tests are additional
  opt-in gates, not substitutes for fake-backed deterministic parity tests.
- NFR-LLM-CARET-FULL-003: Hot request paths must avoid repeated full-tree scans,
  repeated source parsing, and per-request subprocesses unless explicitly
  justified in the row implementation note and measured.
- NFR-LLM-CARET-FULL-004: Each feature group must expose observability for
  latency, errors, retry decisions, token/cost accounting, and cache invalidation
  where the Claude source has equivalent behavior.
- NFR-LLM-CARET-FULL-005: Generated matrices are authoritative. A full-parity
  completion claim must run the plan checker and all row-level test gates.
