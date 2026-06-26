# Spec: vLLM Live Environment Evidence

Source: `test/01_unit/app/llm_runtime/vllm_live_environment_spec.spl`

## Behavior

- Reports `skipped` when local vLLM and GPU are both missing.
- Reports `skipped` when vLLM exists but GPU is missing.
- Reports `skipped` when GPU exists but local vLLM is missing.
- Reports `ready` when both local vLLM and GPU availability are observed.
- Redacts sensitive GPU labels from public JSONL evidence.
- Keeps public evidence free of internal absence markers.

## Covered Requirement

- Static LoRA/live serving evidence can record an explicit skipped state for
  missing local vLLM/GPU without requiring a real installed server or GPU in
  unit tests.

## Not Covered

- Probing the host for `vllm`.
- Probing CUDA/ROCm devices.
- Running a live `/v1/models` request.
