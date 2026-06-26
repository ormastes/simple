# LLM Runtime Control Release Binary Smoke Specification

Manual companion for
`test/03_system/feature/app/cli/llm_runtime_control_binary_smoke_spec.spl`.

## Purpose

This system smoke proves the tracked release Simple binary ships the
`llm-runtime-control` top-level command. It closes the stale-artifact failure
where `release/x86_64-unknown-linux-gnu/simple llm-runtime-control ...` treated
`llm-runtime-control` as a missing source file.

## Covered Behavior

- `release/x86_64-unknown-linux-gnu/simple` exists.
- The release binary dispatches `llm-runtime-control`.
- The preflight command emits
  `llm_runtime_vllm_dashboard_control_execution` JSONL.
- Missing local vLLM/GPU resources render as explicit skipped evidence.
- Public output does not expose the internal absence marker, the base model
  value, or `file not found: llm-runtime-control`.

## Verification

```bash
release/x86_64-unknown-linux-gnu/simple test test/03_system/feature/app/cli/llm_runtime_control_binary_smoke_spec.spl --mode=interpreter --clean
```

