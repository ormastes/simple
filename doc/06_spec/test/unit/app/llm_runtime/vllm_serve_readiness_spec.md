# Spec: vLLM Serve Readiness Orchestration

Source: `test/unit/app/llm_runtime/vllm_serve_readiness_spec.spl`

## Behavior

- Mirrors the canonical unit coverage for serve-readiness orchestration.
- Preflights planned serve and models-probe work without side effects.
- Summarizes already-observed lifecycle and models transport evidence.
- Keeps unknown process state, invalid endpoint plans, and failed startup states
  out of `ready`.
- Mirrors policy-driven sequence coverage for ready, wait-before-probe, spawn
  failure, timeout cleanup, and auth-rejection cleanup paths.
- Emits public JSONL without internal absence markers.

## Covered Requirement

- Mirrored unit evidence for the pure readiness orchestration API and synthetic
  sequence seam.

## Not Covered

- Real process startup, live HTTP retries, or GPU serving proof.
