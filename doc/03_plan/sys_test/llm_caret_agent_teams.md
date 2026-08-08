# LLM Caret Agent Teams - System Test Plan

Date: 2026-07-01

## Scope

System coverage focuses on the TUI-readable agent handoff: agent markdown,
skill, MCP server, plugin, `btw`, `side`, mailbox, and inbox visibility. Unit
specs keep covering pure planning, snapshots, VCS parsing, discovery, mailbox,
and launcher helpers.

Excluded: persistent team supervision, live MCP registry discovery, plugin
install execution, background VCS watching, and live team transport.

## Execution

```bash
bin/release/simple test test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl --native
bin/release/simple spipe-docgen test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl --output doc/06_spec --no-index
```

## Traceability

| REQ | Description | Test File | Test Cases | Coverage |
|---|---|---|---|---|
| REQ-006 | SPipe-style agent/skill/MCP/plugin capability lists | `test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl` | 1 | Full |
| REQ-007 | Explicit `btw`/`side` team interaction | `test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl` | 1 | Full |
| REQ-011 | MCP/plugin handoff visibility | `test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl` | 1 | Full |
| REQ-012 | Team mailbox and inbox filtering | `test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl` | 2 | Full |
| REQ-013 | TUI-readable handoff surface | `test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl` | 3 | Full |

Generated manual: `doc/06_spec/test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.md`.

## Pass Criteria

- SSpec has real assertions and no placeholder passes.
- Generated manual is complete with 0 stubs.
- TUI output contains agent, skill, MCP, plugin, `btw`, `side`, broadcast, and direct-message text.
