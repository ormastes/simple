# Spec: svLLM Tensor Byte Range Loader

Source: `test/01_unit/lib/gc_async_mut/svllm/model_loader_tensor_bytes_spec.spl`

## Behavior

- A validated filesystem-backed tensor pack can return the declared byte range
  for a named tensor.
- A tensor byte range may start in one chunk and continue through following
  chunks when its declared total byte length crosses a chunk boundary.
- Missing tensor names return the explicit `tensor_not_found` status.
- Invalid packs, including missing or digest-mismatched chunks, fail before any
  tensor bytes are returned.

## Covered Requirement

- svLLM model loading must prove manifest tensor offsets map to real chunk
  bytes, including sequential chunk spans, without claiming full async
  NVFS/device streaming readiness.

## Not Covered

- Async NVFS scheduling, pinning, or device staging.
- Tensor deserialization into Torch/runtime tensor handles.
