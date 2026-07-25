# LLM Tool Runtime Hardening - Local Research

Date: 2026-07-01

## Scope

Harden the LLM tool runtime lane for:

- OpenCode CLI support in `src/app/llm_caret/opencode_cli.spl`
- process lifecycle safety for externally launched CLI tools
- static vLLM/SGLang serve planning in `src/app/llm_runtime/serve_plan.spl`

## Current Code

OpenCode wrapper:

- builds `opencode run` arguments with JSON output, model, session, attach URL,
  auto approval, and prompt-last ordering
- starts long-running processes through `app.io.mod.process_spawn_async`
- checks/kills only by PID through `process_is_running` and `process_kill`
- rejects `pid <= 0` before signalling
- parses JSON string fields with a small local scanner shared by content and
  `sessionID`

vLLM/SGLang serve plan:

- keeps execution static; tests build command metadata without starting servers
- redacts model paths and endpoints in command previews
- supports vLLM `--tensor-parallel-size` and `--data-parallel-size`
- supports SGLang `python -m sglang.launch_server`, `--tp`, `--dp`, and
  `--mem-fraction-static`

## Test Evidence

Executable specs:

- `test/01_unit/app/llm_caret/opencode_cli_spec.spl`
- `test/unit/app/llm_caret/opencode_cli_spec.spl`
- `test/01_unit/app/llm_runtime/vllm_readiness_spec.spl`
- `test/unit/app/llm_runtime/vllm_readiness_spec.spl`

Generated/manual evidence:

- `doc/06_spec/01_unit/app/llm_caret/opencode_cli_spec.md`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_readiness_spec.md`

## Gaps

- Final feature/NFR requirements are intentionally not selected here; see the
  options docs.
- `bin/simple check` is currently unavailable in this conflicted checkout.
- The repo-local `$sp_dev` skill file is absent.
