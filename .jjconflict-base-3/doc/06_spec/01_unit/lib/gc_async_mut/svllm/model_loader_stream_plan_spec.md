# Spec: svLLM Tensor Stream Plan

Source: `test/01_unit/lib/gc_async_mut/svllm/model_loader_stream_plan_spec.spl`

## Behavior

- A validated filesystem-backed tensor pack can produce a plan-only read plan
  for a named tensor.
- Single-chunk tensors produce one segment with chunk path, chunk offset, byte
  length, and tensor offset.
- Cross-chunk tensors produce ordered read segments across following chunks.
- Pinning and device-staging requests are carried as intent flags.
- The execution status is `plan_only_not_scheduled`; this spec does not claim
  async NVFS execution.
- Missing tensor names return `tensor_not_found`.

## Covered Requirement

- svLLM model loading must expose deterministic streamer-facing read segments
  before the native NVFS scheduler and pinned/device staging adapter are ready.

## Not Covered

- Issuing `NvfsClient.read_range` calls.
- Registering pinned host/device buffers.
- Scheduling concurrent reads or staging bytes into Torch/runtime tensors.
