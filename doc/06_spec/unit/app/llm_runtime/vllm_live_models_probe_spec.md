# Spec: vLLM Live Models Response Probe

Source: `test/unit/app/llm_runtime/vllm_live_models_probe_spec.spl`

## Behavior

- Mirrors the primary unit spec for already-fetched `/v1/models` response
  parsing.
- Covers ready, auth-rejected, malformed-response, base-model-missing, invalid
  endpoint, and redacted-sensitive-model cases.

## Not Covered

- Live HTTP transport or `vllm serve` lifecycle management.
