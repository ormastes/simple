# Spec: vLLM Live Chat Response Probe

Source: `test/01_unit/app/llm_runtime/vllm_live_chat_probe_spec.spl`

## Behavior

- Parses already-fetched `/v1/chat/completions` response bodies from
  vLLM-compatible endpoints.
- Reports `ready` when HTTP 200 returns at least one choice with assistant
  content.
- Distinguishes auth rejection, malformed response bodies, invalid endpoints,
  empty choices, and missing assistant content.
- Records choice count, content presence, and finish-reason status.
- Emits JSONL evidence without exposing generated assistant content or internal
  absence markers.

## Covered Requirement

- The live vLLM lane has deterministic, absence-safe chat response parsing
  before adding an HTTP client or process supervisor.

## Not Covered

- Performing HTTP POST.
- Starting or supervising `vllm serve`.
- Evaluating generated answer quality.
- Proving GPU-backed serving latency or CUDA placement.
