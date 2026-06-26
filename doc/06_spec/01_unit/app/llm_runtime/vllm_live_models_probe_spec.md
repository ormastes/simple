# Spec: vLLM Live Models Response Probe

Source: `test/01_unit/app/llm_runtime/vllm_live_models_probe_spec.spl`

## Behavior

- Parses already-fetched `/v1/models` response bodies from vLLM-compatible
  endpoints.
- Reports `ready` when HTTP 200 returns a model id matching the configured base
  model.
- Redacts sensitive or path-like model identifiers in public evidence while
  still matching them internally.
- Distinguishes auth rejection, malformed response bodies, invalid endpoints,
  and endpoints that do not serve the requested base model.
- Emits JSONL evidence without exposing `nil`.

## Covered Requirement

- The live vLLM lane has a deterministic, absence-safe response parser before
  adding an HTTP client or process supervisor.

## Not Covered

- Starting or supervising `vllm serve`.
- Fetching `/v1/models` over HTTP.
- Calling `/v1/chat/completions`.
- Proving GPU-backed serving latency or CUDA placement.
