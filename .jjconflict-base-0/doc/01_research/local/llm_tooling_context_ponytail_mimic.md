# Local Research: LLM Tooling Context/Ponytail Mimic

Date: 2026-06-25

## Scope

Build repo-native LLM tooling that can mimic the useful local workflows of
context-mode and ponytail, then replace ad hoc external dependence with Simple
commands, specs, and dashboard evidence.

## Current State

Existing context entrypoint:

- `src/app/context/main.spl`
- CLI usage: `context <file.spl> [target] [options]`
- Existing flags include `--json`, `--text`, `--stats`, `--format=...`, `-o`,
  and shared log/progress options.
- `test/02_integration/app/context_log_modes_spec.spl` covers help, JSON error
  mode, dot progress, and invalid log mode.

Existing implementation gap:

- `src/app/context/main.spl` delegates real work to `app.io.cli_ops` functions
  `context_generate` and `context_stats`.
- `src/app/io/cli_ops.spl` currently returns empty text for both functions.
- `src/app/io/mod_stub.spl` explicitly labels context generation/stats as
  unavailable without SFFI in stub mode.
- Older tracking in
  `doc/02_requirements/language/stdlib/tooling_implementation.md` marks
  `context_pack` as skipped/low-priority.

Existing dashboard foundation:

- `src/app/llm_dashboard/collectors/diagnostics_jsonl_collector.spl`
  summarizes LLM diagnostics JSONL and now handles nested hook fields.
- `src/app/web_dashboard/server.spl` renders a diagnostics panel for
  authenticated dashboard HTML.
- Nil must not be rendered literally in user-facing text, JSON, HTML, MCP
  output, or dashboard panels.

Existing MCP surface:

- Sidecar research found `simple_context` is already present in the app MCP path.
- `simple_ponytail` handler code exists in app MCP lazy query tools, but is not
  surfaced through the public app MCP query registry/static listing.
- Lower runtime MCP modules have fuller context/ponytail schemas; app MCP should
  reuse those shapes where practical instead of inventing a new schema.

## Context-Mode Behaviors To Mimic

Observed from installed tools and repo rules:

- Run batches of commands and return only selected/query-relevant output.
- Index/fetch content without flooding the LLM conversation with raw bytes.
- Provide a search/query surface over stored content.
- Support insight/status views for tool usage and session activity.

For Simple, the first replacement should be a local context pack generator, not
a full background indexing daemon. The smallest useful slice is to make the
existing `simple context` path produce non-empty markdown/text/JSON packs and
stats from a file, with nil-free output.

## Ponytail Behaviors To Mimic

Ponytail is a process policy, not a runtime service:

- Prefer existing code, standard library, and deletion over new abstractions.
- Reject speculative scaffolding.
- Leave one focused runnable check for non-trivial logic.
- Mark intentional simplifications with a short `ponytail:` comment only when a
  shortcut has a known ceiling.

For Simple, the first replacement should be a lightweight review/report mode,
not a new AI agent. It can inspect context-pack output or diffs and report
delete/simplify recommendations.

## Risks

- JSON and brace-heavy strings are fragile in Simple string interpolation; tests
  must cover JSON output directly.
- Existing `cli_ops.spl` has raw runtime/process/env externs because it is a CLI
  owner module. New implementation should reuse its local helpers and avoid
  adding new raw `rt_*` shortcuts.
- User-visible absence must be rendered as empty/omitted/domain text, never
  literal `nil`.
- Full indexing/search daemon work is larger than the first slice and should not
  be mixed with context generation.

## Recommended First Slice

Implement `context_generate` and `context_stats` in `src/app/io/cli_ops.spl`
using existing file read helpers:

- Markdown/text pack containing source, target, selected lines, and token
  estimate.
- JSON pack with status/source/target/line/token fields and escaped content.
- Stats output with source line count, selected line count, and estimated tokens.
- Focused unit/integration specs proving non-empty output and no visible `nil`.

Follow-on slice:

- Expose the existing `simple_ponytail` handler through app MCP tool
  registry/static listing.
- Add discoverability and callability coverage.
- Keep output nil-free and avoid new raw runtime shortcuts.
