# Agent Orchestrator — Plan

## Objective

Implement the LLM CLI tools agent orchestrator in `examples/llm_cli_tools/` so that
the `/impl` workflow can spawn codex (verification) and gemini (design) subagents.

## Current Status

| Component | Status | Evidence |
|-----------|--------|----------|
| examples/llm_cli_tools/src/app/agent/orchestrator.spl | Real | spawn/result/list commands working |
| examples/llm_cli_tools/test/unit/agent/orchestrator_spec.spl | Real | 9/9 tests pass |
| codex CLI binary | Installed | `which codex` → /home/ormastes/.npm-global/bin/codex |
| gemini CLI binary | Installed | `which gemini` → /home/ormastes/.npm-global/bin/gemini |
| impl skill integration | Real | `.claude/skills/impl.md` spawn commands point to orchestrator |

## What Was Done

1. Created orchestrator `src/app/agent/orchestrator.spl` (done)
   - Self-contained for interpreter mode (all extern declarations inline)
   - Env var reading and command dispatch (spawn/result/list)
   - Provider binary resolution: codex → `codex exec`, gemini → `gemini -p --yolo`
   - Process execution via rt_process_run
   - File-based result storage in `data/agents/`

2. Created unit test `test/unit/agent/orchestrator_spec.spl` (done)
   - Provider resolution (3 tests)
   - Arg building (4 tests)
   - Result path construction (1 test)
   - Result storage round-trip (1 test)

3. Updated `.claude/skills/impl.md` CLI flags to match real tools (done)
   - codex: `exec` subcommand (was `--full-auto --quiet`)
   - gemini: `-p --yolo` (was `--sandbox off`)

## Architecture

Single-file orchestrator (interpreter mode), following simple_aidev patterns:

```
orchestrator.spl
  ├── extern declarations (rt_process_run, rt_env_get, etc.)
  ├── provider config (_provider_binary, _build_args)
  ├── result storage (_save_result, _load_result)
  ├── commands (_cmd_spawn, _cmd_result, _cmd_list)
  └── entry point (main)
```

## Related

- [Requirement](../requirement/agent_orchestrator.md)
- [Impl Skill](../../.claude/skills/impl.md)
