# Spec: vLLM Live Request Plan

Source: `test/01_unit/app/llm_runtime/vllm_live_request_plan_spec.spl`

## Behavior

- Builds sanitized plan-only request metadata for `/v1/models`.
- Builds sanitized plan-only request metadata for `/v1/chat/completions` when a
  request body is present.
- Removes endpoint credentials from public URL previews.
- Rejects invalid endpoints before creating transport metadata.
- Reports missing chat bodies without exposing request content.
- Blocks unsupported chat parameters before transport.

## Covered Requirement

- The live vLLM lane has a deterministic request-planning boundary before an
  HTTP client or vLLM process supervisor is added.

## Not Covered

- Performing HTTP GET or POST.
- Starting or supervising `vllm serve`.
- Validating actual chat completion responses.
- Proving GPU-backed serving latency or CUDA placement.
