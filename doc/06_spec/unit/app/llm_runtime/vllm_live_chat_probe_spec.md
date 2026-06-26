# Spec: vLLM Live Chat Response Probe

Source: `test/unit/app/llm_runtime/vllm_live_chat_probe_spec.spl`

## Behavior

- Mirrors the primary unit spec for already-fetched `/v1/chat/completions`
  response parsing.
- Covers ready, auth-rejected, malformed-response, empty-choice,
  missing-content, invalid-endpoint, and generated-content-redaction cases.

## Not Covered

- Live HTTP transport or `vllm serve` lifecycle management.
