# Spec: vLLM Serve Lifecycle Wrapper

Source: `test/01_unit/app/llm_runtime/vllm_serve_lifecycle_spec.spl`

## Behavior

- Does not spawn `vllm serve` when static serve planning fails.
- Adapts spawned process ids into public lifecycle evidence.
- Reports spawn failures explicitly.
- Reports invalid process ids as not running.
- Refuses to kill invalid process ids.
- Emits lifecycle JSONL without internal absence markers.

## Covered Requirement

- The live vLLM lane has a narrow lifecycle wrapper that reuses the existing
  process facade instead of importing raw runtime process calls.

## Not Covered

- Proving `vllm` is installed.
- Proving the process has reached HTTP readiness.
- GPU/CUDA serving evidence.
