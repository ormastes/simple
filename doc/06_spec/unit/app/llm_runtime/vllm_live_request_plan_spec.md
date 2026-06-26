# Spec: vLLM Live Request Plan

Source: `test/unit/app/llm_runtime/vllm_live_request_plan_spec.spl`

## Behavior

- Mirrors the primary request-plan spec for sanitized `/v1/models` and
  `/v1/chat/completions` request metadata.
- Covers invalid endpoints, missing chat bodies, unsupported chat parameters,
  URL credential redaction, and plan-only execution status.

## Not Covered

- Live HTTP transport or `vllm serve` lifecycle management.
