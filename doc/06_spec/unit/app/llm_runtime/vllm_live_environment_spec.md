# Spec: vLLM Live Environment Evidence

Source: `test/unit/app/llm_runtime/vllm_live_environment_spec.spl`

## Behavior

- Mirrors skipped and ready live-environment evidence coverage.
- Verifies sensitive GPU labels are redacted.
- Keeps public evidence free of internal absence markers.

## Covered Requirement

- Mirrored unit evidence for the live vLLM/GPU skipped-state classifier.

## Not Covered

- Real host binary or GPU probing.
