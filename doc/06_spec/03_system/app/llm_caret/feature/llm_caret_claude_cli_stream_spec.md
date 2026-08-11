# LLM Caret Claude CLI Stream Contract

**Requirement IDs:** REQ-LLM-CARET-CLI-HARDEN-006
**Plan:** `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md`
**Evidence:** `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream/`
**Execution status:** Not executed in this change. A qualified self-hosted
Simple runtime is required; the Rust seed and source fallback are not
acceptance evidence.

## Scope and claim boundary

These deterministic scenarios call production `claude_cli_stream` with the
repository's offline Claude fixture. They prove parsing and ordering of stream
envelopes, provider-error redaction, and fail-closed malformed/terminal-state
handling. They do not prove cached `bin/caret` wrapper behavior, TUI rendering,
an installed Claude executable, authentication, or live provider access.

The runner should retain textual execution evidence beneath the path above.
This is a direct function contract, not a terminal-screen capture; the PTY
spec owns ANSI `typescript.txt` captures.

## REQ-LLM-CARET-CLI-HARDEN-006 — production Claude stream handling

### should preserve a complete ordered provider stream

1. **Prepare offline Claude CLI fixture** — confirm the deterministic fixture
   executable is present.
2. **Stream the provider response** — invoke production `claude_cli_stream`
   with `fixture-stream`.
3. **Check ordered events and redaction** — require `system`, `assistant`, and
   terminal `result` in order, with the fixture session, text, and output-token
   count intact.

### should redact a structured provider error from the stream

1. **Prepare offline Claude CLI fixture** — confirm the deterministic fixture
   executable is present.
2. **Stream the provider response** — invoke production `claude_cli_stream`
   with the structured provider-error fixture.
3. **Check ordered events and redaction** — require exactly one terminal error,
   retain the safe provider message and redaction marker, and forbid the fixture
   secret from the returned content.

### should reject malformed and duplicate-terminal provider streams

1. **Prepare offline Claude CLI fixture** — confirm the deterministic fixture
   executable is present.
2. **Stream the provider response** — invoke the malformed-then-result and
   duplicate-terminal fixtures through production `claude_cli_stream`.
3. **Check ordered events and redaction** — require one invalid error for each
   input, retaining the malformed-JSON and post-terminal rejection reasons.

## Executable SSpec

The executable source is
`test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl`.
Run SPipe docgen with a qualified self-hosted runtime before changing this
manual's execution status.
