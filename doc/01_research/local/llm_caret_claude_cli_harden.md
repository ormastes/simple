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

## 2026-07-25 continuation findings

The original bounded map now covers 25 direct Caret files, 7,487 LOC, and 516
declarations exactly. That result is still only a map.

The separate Claude-full parts bin contains 848 source files and 349 specs.
A fresh lexical triage found 7,009 top-level functions, including 3,007 without
a call-like test/reference occurrence and 666 ledger-named functions. Name
collisions and indirect dispatch make these triage counts, not behavioral
coverage percentages.

The old direct-TUI gap list is stale: injected runtime tests now call
`caret_chat`, `_inner_height`, `_draw_frame`, `_read_line`, `run_chat_tui`, and
`run_chat_plain`. The remaining live boundary is `production_caret_io` plus a
provenance-checked cached Caret process.

Highest-value direct gaps are shipped entry/provider transports first
(`main`, OpenAI-compatible, Claude API, OpenAI API, config, OpenCode, local
torch), then live TUI, bridge entry/transport callbacks, MCP result mapping,
and remaining OAuth redaction/error/flow/step-up owners.

The current CLI round closes the static direct-owner gaps for injected
`main` entry orchestration, OpenAI-compatible, Claude API, OpenAI API, and
config file/API-key ownership. Both API sends retain retry semantics rather
than collapsing them to one total network attempt. The next shipped CLI owners
are OpenCode process/send behavior and local-torch cleanup; live TUI remains
after those CLI owners.
