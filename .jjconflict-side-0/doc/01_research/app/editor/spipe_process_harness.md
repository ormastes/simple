<!-- codex-research -->
# SPipe Process Harness Local Research

## Scope

Build production-level SPipe process harness infra for Codex, Claude, and Gemini with common hooks, skill deploy output, a CLI HUD, durable goal state, and prevention gates.

## Existing Repo Findings

- `.claude/skills/sstack.md` (the SStack/SPipe orchestrator) defines durable `.spipe/<feature>/state.md` workflow state and user confirmation gates.
- `src/app/llm_diag_hook/main.spl` already handles Claude hook JSON and appends JSONL diagnostics.
- `src/lib/nogc_async_mut/llm_diagnostics/hook_handler.spl` provides JSON field extraction and hook parsing helpers.
- `src/app/llm_process_gen/main.spl` provides the pattern for generated LLM process artifacts.
- `src/app/llm_dashboard/tui/status_bar.spl` already renders provider/token status; HUD work should remain compact and CLI-safe.
- `.gemini/settings.json` has an empty `hooks` object; `.claude/settings.json` has no hooks configured.

## Design Implication

The harness should be a small common Simple library used by provider hooks and a CLI app. Provider-specific deploy output should be generated from shared data so Codex, Claude, and Gemini do not fork prevention or event-log logic.

