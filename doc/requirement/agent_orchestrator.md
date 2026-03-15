# Agent Orchestrator — Requirement

## Feature

LLM CLI Tools Agent Orchestrator — spawns `codex` and `gemini` CLI tools as
verification/design subagents for the `/impl` workflow.

## Motivation

The impl skill (17-phase workflow) requires automated plan verification (Phase 4v, 6v)
and visual design generation (Phase 4g). These tasks are delegated to external LLM CLIs:

- **Codex** (`codex --full-auto --quiet`) — verifies plan accuracy, test coverage, dummy detection
- **Gemini** (`gemini --sandbox off`) — produces UI layouts, wireframes, visual concepts

Currently no orchestrator exists to spawn these tools. The impl skill documents the
interface but nothing implements it.

## Scope

**In scope:**
- Environment-variable-driven CLI interface (`AGENT_CMD`, `AGENT_PROVIDER`, etc.)
- Spawn codex/gemini with system prompt + prompt file content
- File-based result storage with unique agent IDs
- Result retrieval and listing commands

**Out of scope:**
- TUI interface (future work, scaffold exists)
- Async/parallel agent execution
- Session resumption for agents
- HTTP-based providers (covered by simple_aidev)

## I/O Examples

### Spawn codex verifier
```bash
AGENT_CMD=spawn AGENT_PROVIDER=codex_cli AGENT_ROLE=verify \
  AGENT_SYSTEM="You are a plan verification agent." \
  AGENT_PROMPT_FILE=doc/plan/feature.md \
  ../../bin/release/simple run src/app/agent/orchestrator.spl
```
Output:
```
Spawning codex_cli (verify)...
AGENT_ID=codex_cli_verify_1710500000
---
STATUS_CHECK:
  - module_x: PASS
OVERALL: PASS
```

### Spawn gemini designer
```bash
AGENT_CMD=spawn AGENT_PROVIDER=gemini_cli AGENT_ROLE=design \
  AGENT_SYSTEM="You are a UI/visual design agent." \
  AGENT_PROMPT_FILE=doc/design/feature.md \
  ../../bin/release/simple run src/app/agent/orchestrator.spl
```

### Retrieve result
```bash
AGENT_CMD=result AGENT_ID=codex_cli_verify_1710500000 \
  ../../bin/release/simple run src/app/agent/orchestrator.spl
```

### List results
```bash
AGENT_CMD=list ../../bin/release/simple run src/app/agent/orchestrator.spl
```

## Acceptance Criteria

1. `AGENT_CMD=spawn` reads env vars, spawns the correct CLI tool, saves output
2. `AGENT_CMD=result` retrieves and prints stored result by ID
3. `AGENT_CMD=list` lists all stored agent results
4. Error handling for missing env vars, missing files, failed processes
5. Results persist in `data/agents/` directory as text files
6. Works in interpreter mode (`simple run`)

## Dependencies

- `rt_process_run` runtime function (confirmed working)
- `rt_env_get`, `rt_file_read_text`, `rt_file_write_text` runtime functions
- `codex` and `gemini` CLI binaries installed on system

## Related

- [Plan](../plan/agent_orchestrator.md)
- [Impl Skill](../../.claude/skills/impl.md) — Phase 4g, 4v, 6v
- [simple_aidev](../../examples/simple_aidev/) — reference implementation for LLM providers
