# LLM Tool Runtime Hardening - Feature Requirements

Date: 2026-07-01
Selected option: A - Minimal CLI Wrapper Hardening

## Requirements

### REQ-001 OpenCode Run Arguments

The OpenCode wrapper must build documented `opencode run` arguments without
shell command strings.

Acceptance:

- command starts with `run`
- output format defaults to `json`
- model, session, attach URL, auto approval, extra args, and prompt are
  represented as structured argv entries
- prompt remains the final argument

Evidence:

- `src/app/llm_caret/opencode_cli.spl`
- `test/01_unit/app/llm_caret/opencode_cli_spec.spl`
- `doc/06_spec/01_unit/app/llm_caret/opencode_cli_spec.md`

### REQ-002 OpenCode Local Process Lifecycle

The OpenCode wrapper must expose local process lifecycle primitives matching the
Claude-CLI-like tool surface: spawn, running-status check, and PID kill.

Acceptance:

- spawn uses the existing process facade
- running-status uses the existing process facade
- kill uses the existing process facade
- invalid PIDs are rejected before signalling

Evidence:

- `src/app/llm_caret/opencode_cli.spl`
- `test/01_unit/app/llm_caret/opencode_cli_spec.spl`

### REQ-003 OpenCode Response Parsing

The OpenCode wrapper must parse simple JSON responses needed by the provider
path without requiring the OpenCode binary in unit tests.

Acceptance:

- `content` is extracted from JSON output
- `sessionID` is extracted and exposed as `session_id`
- empty output returns an error response

Evidence:

- `src/app/llm_caret/opencode_cli.spl`
- `test/01_unit/app/llm_caret/opencode_cli_spec.spl`

### REQ-004 Backend-Native Static Serve Plans

The LLM runtime serve planner must generate static command metadata using
backend-native flags without starting vLLM or SGLang servers.

Acceptance:

- vLLM plans use vLLM-native serve flags
- SGLang plans use `python -m sglang.launch_server`
- SGLang tensor parallelism uses `--tp`
- SGLang data parallelism uses `--dp`
- SGLang memory tuning uses `--mem-fraction-static`

Evidence:

- `src/app/llm_runtime/serve_plan.spl`
- `test/01_unit/app/llm_runtime/vllm_readiness_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_readiness_spec.md`

## Out Of Scope

- managed PID registry
- live OpenCode, vLLM, or SGLang startup tests
- production supervisor, timeout, RSS, and log ownership
