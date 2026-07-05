# LLM Caret Claude CLI Harden - Local Research

Date: 2026-07-05

## Findings

- `src/app/llm_caret` already owns a provider caret with Claude CLI, Claude API,
  OpenAI, OpenAI-compatible, local torch, OpenCode, config, server, and shared
  type/helper files.
- Existing unit tests cover most pure provider behavior under
  `test/01_unit/app/llm_caret`.
- Existing live specs under `test/03_system/tools/llm` exercise Claude CLI
  behavior, but their coverage comments still reference an old caret path.
- No trace artifact maps the extracted Claude source under
  `tmp/claude/claude-code-main/src` to each Simple LLM caret source file.

## Chosen Local Scope

Add traceability and a computed mapping gate before attempting broad behavior
ports. This gives later migration work a concrete source map and keeps this
lane small.
