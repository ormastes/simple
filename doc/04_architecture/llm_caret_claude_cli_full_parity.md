# LLM Caret Claude CLI Full Parity - Architecture

Date: 2026-07-05

## Decision

Use a new MDSOC+ mirror capsule under `src/app/llm_caret/claude_full/`.
Each Claude source file maps to one Simple target file with the same relative
path and `.spl` extension. Existing `src/app/llm_caret/*.spl` files remain the
stable public facade; the full-parity capsule plugs into that facade only after
its row-level gates pass.

## Capsules

- `llm_caret.claude_full.entrypoints`: CLI entry, SDK entry, MCP entry.
- `llm_caret.claude_full.core`: Query engine, tasks, tools, schemas, state.
- `llm_caret.claude_full.commands`: slash commands and command handlers.
- `llm_caret.claude_full.tools`: tool definitions, permission, validation,
  execution, and result storage.
- `llm_caret.claude_full.terminal_ui`: components, Ink renderer parity, screens,
  hooks, vim, buddy, voice, and status surfaces.
- `llm_caret.claude_full.remote_bridge`: bridge, remote, upstream proxy,
  session runner, trusted device, and transport code.
- `llm_caret.claude_full.services`: API services, auto/dream/memory/plugin,
  skill, output style, telemetry, and migrations.
- `llm_caret.claude_full.support`: constants, utils, context, native-ts,
  state helpers, and platform utilities.

## Public Boundary

The existing public entry points stay boring:

- `src/app/llm_caret/mod.spl` exposes initialization and chat/send APIs.
- `src/app/llm_caret/provider.spl` dispatches providers.
- `src/app/llm_caret/claude_cli.spl` remains the compact stable wrapper.
- Full parity is imported through explicit adapter functions only after tests
  prove row coverage.

## No-Skip Rule

`doc/03_plan/trace/llm_caret_claude_cli_full_parity_file_matrix.tsv` and
`doc/03_plan/trace/llm_caret_claude_cli_full_parity_symbol_matrix.tsv` are the
source of truth. A source file or symbol not implemented is not a warning; it is
a release blocker.
