# Spec: vLLM Live HTTP Transport Wrapper

Source: `test/unit/app/llm_runtime/vllm_live_transport_spec.spl`

## Behavior

- Mirrors the primary transport-wrapper spec.
- Covers deterministic response adaptation and no-fetch behavior for invalid or
  unsafe request plans.

## Not Covered

- Live endpoint availability or `vllm serve` lifecycle management.
