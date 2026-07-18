# Spec: Torch Device Placement Status

Source: `test/01_unit/lib/common/torch/torch_device_placement_status_spec.spl`

## Behavior

- GC and NoGC backend `tensor_cuda(h, device_id)` methods pass the requested
  device id through to the Torch SFFI instead of forcing CUDA device `0`.
- GC and NoGC `Tensor.cuda(device_id)` methods pass the requested device id
  through to the Torch SFFI instead of forcing CUDA device `0`.
- GC and NoGC Torch stream creation passes the requested device id through to
  `rt_torch_stream_create`.
- GC and NoGC optimizer state initialization no longer moves state tensors to
  CUDA device `0` implicitly.
- GC and NoGC optimizer state initialization queries the parameter device with
  `rt_torch_torchtensor_device(param)` and moves zero state tensors to that same
  CUDA device when the parameter is already CUDA-backed.

## Covered Requirement

- Torch device placement must not be user-visible as correct when it is actually
  hardcoded to CUDA device `0`.
- Optimizer momentum and Adam state must preserve the parameter device for
  already-CUDA parameters instead of falling back to CPU/default state.

## Not Covered

- Live CUDA placement against libtorch.
- End-to-end optimizer execution against a live libtorch CUDA installation.
