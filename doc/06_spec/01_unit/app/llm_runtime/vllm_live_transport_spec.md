# Spec: vLLM Live HTTP Transport Wrapper

Source: `test/01_unit/app/llm_runtime/vllm_live_transport_spec.spl`

## Behavior

- Uses the app-owned HTTP facade boundary for live vLLM GET/POST requests.
- Summarizes fetched `/v1/models` responses without exposing response bodies.
- Summarizes fetched `/v1/chat/completions` responses without exposing
  generated assistant content.
- Does not fetch when request planning fails because of invalid endpoints,
  missing chat bodies, or unsupported chat parameters.
- Emits JSONL evidence with transport status, HTTP status, path, and parser
  status only.

## Covered Requirement

- The live vLLM lane has a narrow transport wrapper that reuses existing app I/O
  facades instead of adding raw runtime calls or shelling out.

## Not Covered

- Starting or supervising `vllm serve`.
- Proving a real local endpoint is available.
- Proving GPU-backed serving latency or CUDA placement.
