# Agent Orchestrator — Plan

## Objective

Implement the LLM CLI tools agent orchestrator in `examples/llm_cli_tools/` so that
the `/impl` workflow can spawn codex (verification) and gemini (design) subagents.

## Current Status

| Component | Status | Evidence |
|-----------|--------|----------|
| examples/llm_cli_tools/ | Scaffold only | Empty directories, no .spl files |
| src/app/agent/orchestrator.spl | Missing | Directory does not exist |
| codex CLI binary | Installed | `which codex` → /home/ormastes/.npm-global/bin/codex |
| gemini CLI binary | Installed | `which gemini` → /home/ormastes/.npm-global/bin/gemini |
| simple_aidev providers | Real | Reference patterns for rt_process_run usage |

## What To Do

1. Create orchestrator entry point `src/app/agent/orchestrator.spl` (difficulty: 2)
   - Self-contained for interpreter mode (all extern declarations inline)
   - Env var reading and command dispatch
   - Provider binary resolution and arg building
   - Process execution via rt_process_run
   - File-based result storage

2. Create unit test `test/unit/agent/orchestrator_spec.spl` (difficulty: 1)
   - Test provider resolution
   - Test arg building
   - Test result storage round-trip

## Dependencies

Task 2 depends on Task 1.

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
