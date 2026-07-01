# LLM Tool Runtime Hardening Guide

Date: 2026-07-01

## Scope

This guide covers the selected A+A lane for the LLM tool runtime hardening work:

- LLM Caret (`src/app/llm_caret/`) as the primitive Claude-like LLM app layer
- OpenCode as a Claude-CLI-like provider surface in `llm_caret`
- PID-based OpenCode lifecycle helpers
- static vLLM and SGLang serve-plan metadata
- deterministic unit/check/docgen verification

## LLM Caret Status

The primitive Claude-like app layer is named **LLM Caret** and lives at
`src/app/llm_caret/`. It provides chat state, provider dispatch, Claude CLI/API,
OpenAI/OpenAI-compatible, local torch, and OpenCode wrappers.

It is not a Claude Code CLI replacement yet: there is no registered top-level
`simple llm` command, no agent/tool loop, and no direct `goal` or `advisor`
command surface. Add those only when a lane explicitly selects a real CLI
contract.

## OpenCode CLI

Use `src/app/llm_caret/opencode_cli.spl` for OpenCode-specific command
construction and lifecycle helpers.

Required behavior:

- build `opencode run` as structured argv, not shell text
- default output format to `json`
- keep the prompt as the last argument
- pass model, session, attach URL, auto approval, and extra args as argv entries
- expose spawn, running-status, and PID kill helpers
- reject `pid <= 0` before signalling
- parse `content` and `sessionID` from JSON output

Default verification:

```bash
bin/simple test test/01_unit/app/llm_caret/opencode_cli_spec.spl --mode=interpreter
bin/simple check src/app/llm_caret/opencode_cli.spl
bin/simple spipe-docgen test/01_unit/app/llm_caret/opencode_cli_spec.spl
```

## vLLM and SGLang Serve Planning

Use `src/app/llm_runtime/serve_plan.spl` for static command metadata. These
helpers must not start servers during default verification.

Backend flag contract:

- vLLM: `vllm serve`, `--tensor-parallel-size`, `--data-parallel-size`
- SGLang: `python -m sglang.launch_server`, `--tp`, `--dp`,
  `--mem-fraction-static`

Default verification:

```bash
bin/simple test test/01_unit/app/llm_runtime/vllm_readiness_spec.spl --mode=interpreter
bin/simple check src/app/llm_runtime/serve_plan.spl
bin/simple spipe-docgen test/01_unit/app/llm_runtime/vllm_readiness_spec.spl
```

## Requirement Selection

When using `$sp_dev`, write option docs first. After the user selects options:

1. Write final requirement docs under `doc/02_requirements/feature/` and
   `doc/02_requirements/nfr/`.
2. Delete the unchosen `*_options.md` docs.
3. Refresh `doc/04_architecture`, `doc/05_design`, `doc/03_plan`, `doc/06_spec`,
   and this guide.
4. Run focused tests, `bin/simple check` for changed source files, and
   `bin/simple spipe-docgen` for changed specs.

For this lane the selected scope is A+A: minimal wrapper hardening plus
unit-level safety gates. Live OpenCode/vLLM/SGLang smoke tests and process
supervision are intentionally out of scope until selected by a later
requirement update.
