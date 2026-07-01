# LLM Tool Runtime Hardening - NFR Requirements

Date: 2026-07-01
Selected option: A - Unit-Level Safety Gate

## Requirements

### NFR-001 Deterministic Default Verification

Default verification for this lane must not require installed OpenCode, GPUs,
vLLM, SGLang, credentials, model downloads, or open ports.

Evidence:

- `test/01_unit/app/llm_caret/opencode_cli_spec.spl`
- `test/01_unit/app/llm_runtime/vllm_readiness_spec.spl`

### NFR-002 No Shell Kill Shortcuts

OpenCode argument construction must not inject shell lifecycle shortcuts such as
`kill` or `pkill`.

Evidence:

- `test/01_unit/app/llm_caret/opencode_cli_spec.spl`

### NFR-003 Invalid PID Safety

OpenCode process stopping must reject invalid PIDs before signalling through the
process facade.

Evidence:

- `src/app/llm_caret/opencode_cli.spl`
- `test/01_unit/app/llm_caret/opencode_cli_spec.spl`

### NFR-004 Static Planning Safety

Serve-plan tests must verify static metadata generation and must not start live
vLLM or SGLang servers.

Evidence:

- `src/app/llm_runtime/serve_plan.spl`
- `test/01_unit/app/llm_runtime/vllm_readiness_spec.spl`

### NFR-005 Sensitive Preview Redaction

Static serve-plan previews and evidence must not expose private model paths,
adapter paths, passwords, or endpoints.

Evidence:

- `test/01_unit/app/llm_runtime/vllm_readiness_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_readiness_spec.md`

## Out Of Scope

- opt-in live smoke gates
- production process supervision gates
