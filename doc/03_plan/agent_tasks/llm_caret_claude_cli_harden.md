# LLM Caret Claude CLI Harden - Agent Tasks

Date: 2026-07-05
Updated: 2026-07-07 (retargeted from trace-checker to shipped-path robustness)

## Reset (2026-07-07)

The prior tasks scoped "harden" to a traceability/mapping checker
(`check-llm-caret-claude-cli-trace.shs`) that verifies file/LOC/symbol-name
presence in a report. That is a **documentation-coverage** gate, not robustness.
Real hardening targets the **shipped path** (`src/app/llm_caret/*.spl`, ~3,086
LOC that actually runs), not the `claude_full/` island (unreferenced, no
`fn main`). Design: `doc/05_design/llm_caret_claude_cli_harden.md`.

## Quality Gate (every task)

Interpreter-mode file-load "PASS" is **insufficient** (`.claude/rules/testing.md`:
the runner may not execute `it` blocks). Each acceptance test below must run in
an `it`-executing mode against the fault it is meant to survive, with the true
assertion-level result recorded. Assert on behavior (spawn spy, attempt counter,
transcript scan), not struct fields.

## Tasks (P0 first)

1. **Retry/backoff/timeout** (P0).
   - Scope: `with_retry` around `dispatch_send`; per-attempt timeout on every
     `rt_http_request`/`rt_process_run`; retryable-vs-terminal error type.
   - Files: `provider.spl`, `claude_api.spl`, `claude_cli.spl`, `openai_api.spl`.
   - Acceptance: it-block — 429-then-200 recovers (assert attempts);
     persistent-500 returns terminal error; hung subprocess killed at timeout.
   - Exit: no transient failure surfaces raw; no unbounded subprocess wait.

2. **Secret redaction** (P0).
   - Scope: redaction pass before any logging/JSONL persist of request/response
     bodies (strip `Authorization`, `sk-`/API-key patterns).
   - Files: `provider.spl`, `chat.spl`.
   - Acceptance: it-block — a persisted transcript contains no raw API key.
   - Exit: secrets never reach transcripts/logs.

3. **Injection defense** (P0).
   - Scope: tag/wrap untrusted tool output (WebFetch, file content) before it
     re-enters message history.
   - Files: WebFetch/file-read executors, `chat.spl`.
   - Acceptance: it-block — fetched content is wrapped/tagged in history.
   - Exit: tool output cannot silently steer the loop.

4. **Permission gating** (P0).
   - Scope: single `permission_gate(mode,tool,input)` every tool call traverses
     before execution (allow/ask/deny).
   - Files: dispatch/gate module; wire `bridge/bridgePermissionCallbacks.spl`
     structs; hook into `provider.spl`.
   - Acceptance: it-block — denied Bash does NOT spawn (spawn spy); allowed does;
     nothing executes ungated.
   - Exit: no ungated tool execution.

5. **Crash resilience** (P1).
   - Scope: per-turn JSONL persist + subprocess timeout + top-level error
     boundary with recovery marker.
   - Files: `chat.spl`, `provider.spl`, `claude_cli.spl`.
   - Acceptance: it-block — simulated mid-turn kill; `--resume` recovers
     completed turns.
   - Exit: a crash loses at most the in-flight turn.

6. **Observability** (P1).
   - Scope: structured JSON-lines events around `dispatch_send` (latency, error
     class, retry decisions, token/cost).
   - Files: new logging helper; `provider.spl`.
   - Acceptance: it-block — one dispatch emits an event with all fields.
   - Exit: NFR-LLM-CARET-FULL-004 met.

## Legacy Trace Gate (retained, docs-coverage only)

Keep `scripts/check/check-llm-caret-claude-cli-trace.shs` and
`test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl` as a
documentation-coverage signal only. They must NOT be cited as evidence that any
task above is complete — remove any LOC>=source (size-parity) condition from the
checker so it stops rewarding comment padding.

## Lanes

- P0 tasks (1-4): highest-capability implementer + security review before close.
- P1 tasks (5-6): standard implementer + merge review.
- Final reviewer verifies each acceptance it-block actually executed (not
  file-load PASS) before release.
