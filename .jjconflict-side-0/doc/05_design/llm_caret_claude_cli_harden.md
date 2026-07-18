# LLM Caret Claude CLI Harden - Detail Design

Date: 2026-07-05
Updated: 2026-07-07 (scope correction: hardening targets the shipped path)

## Scope Correction (2026-07-07)

This doc previously described "hardening" as a traceability/mapping checker
(`check-llm-caret-claude-cli-trace.shs`) that verifies file/LOC/symbol-name
presence in a markdown table. That is a **documentation-coverage gate, not a
robustness gate** — it proves a symbol name appears in a report, not that any
transient failure, secret leak, or unsafe tool call is handled.

Real hardening applies to the **shipped path** — the ~3,086-LOC root of
`src/app/llm_caret/` that actually runs (`mod.spl` -> `provider.spl` ->
`claude_api.spl`/`claude_cli.spl`/`openai_api.spl`/...). It does NOT apply to the
`claude_full/` island (~720 files/~151K LOC), which is unreferenced by the
shipped facade and has no `fn main` (see
`doc/05_design/llm_caret_claude_cli_full_parity.md` current-state section).

The traceability report itself (`doc/09_report/llm_caret_claude_cli_traceability.md`)
is honest about its narrow scope ("it is not a full port of Claude Code"). The
overclaim was in reading that mapping gate as a hardening gate. The mapping
checker may remain as a docs-coverage tool, but it is not the hardening gate.

## Hardening Dimensions (shipped path)

Each is designed in full in the parity design doc; here is the hardening view —
what "robust" means and where it lands in the shipped source. Severities from the
2026-07-07 gap analysis.

| Dimension | Severity | Shipped-path landing site | Robustness property |
|---|---|---|---|
| Retry/backoff/timeout | P0 | `provider.spl` `dispatch_send`; every `rt_http_request`/`rt_process_run` site | transient 429/5xx/network failure recovers; hung subprocess is killed |
| Secret redaction | P0 | redaction pass before logging/JSONL persist in `provider.spl`/`chat.spl` | no raw `Authorization`/API key in any transcript or log |
| Injection defense | P0 | tag/wrap untrusted tool output in WebFetch/file-read before re-entering history | fetched content cannot silently steer the loop |
| Permission gating | P0 | single `permission_gate` all tool calls traverse before execution | `deny` blocks a real spawn; nothing executes ungated |
| Crash resilience | P1 | per-turn JSONL persist + subprocess timeout + top-level error boundary | crash loses at most the in-flight turn; `--resume` recovers |
| Observability | P1 | structured JSON-lines events around `dispatch_send` | latency/error/retry/token-cost are emitted |

## Legacy Trace Checker (retained as docs-coverage only)

- `doc/09_report/llm_caret_claude_cli_traceability.md` — feature/file/symbol
  mapping table (narrow scope, honest).
- `scripts/check/check-llm-caret-claude-cli-trace.shs` — counts mapped files/LOC
  and symbol-name presence, fails below 80%. This is a **documentation-coverage**
  signal only; it does not gate robustness and must not be cited as evidence that
  any hardening dimension above is met.
- `test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl` — runs
  the checker and asserts PASS output.

## Hardening Gate (real)

A dimension is hardened only when an **executed it-block** (not interpreter
file-load PASS) asserts the robustness property in the table above against a
fault it is meant to survive — e.g. a mock 429 for retry, a spawn spy for
permission deny, a transcript scan for redaction. See the hardening plan for the
per-task acceptance tests and the interpreter-mode caveat.
