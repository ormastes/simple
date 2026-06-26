# Spec: vLLM Serve Readiness Orchestration

Source: `test/01_unit/app/llm_runtime/vllm_serve_readiness_spec.spl`

## Behavior

- Preflights `vllm serve` and `/v1/models` probe planning without spawning or
  fetching.
- Reports invalid manifests before lifecycle starts.
- Summarizes a running process plus ready models endpoint as `ready`.
- Refuses to treat spawned-but-unpolled lifecycle state as ready.
- Keeps request-planning failures as `not_ready`.
- Provides a default readiness policy and pure synthetic sequence runner.
- Orchestrates to `ready` from synthetic process/running/models observations.
- Waits for `running` before probing models by default.
- Short-circuits spawn failure before synthetic transport evidence.
- Times out after the configured attempt count and marks managed pid cleanup.
- Stops on terminal auth rejection when policy requests cleanup.
- Emits public JSONL without internal absence markers, model ids, prompts, or
  response bodies.

## Covered Requirement

- The live vLLM lane now has a pure orchestration boundary that composes
  lifecycle and transport evidence without requiring a real vLLM server in unit
  tests.
- The later live runner has a policy shape and deterministic sequence seam for
  dashboard and integration evidence.

## Not Covered

- Starting a real `vllm serve` process.
- Retrying until HTTP readiness.
- GPU/CUDA serving evidence.
