# Spec: vLLM Serve Lifecycle Wrapper

Source: `test/unit/app/llm_runtime/vllm_serve_lifecycle_spec.spl`

## Behavior

- Mirrors the primary serve lifecycle wrapper spec.
- Covers no-spawn planning failure, pid adaptation, invalid pid status, and
  invalid pid stop behavior.

## Not Covered

- Live `vllm serve` startup or endpoint readiness.
