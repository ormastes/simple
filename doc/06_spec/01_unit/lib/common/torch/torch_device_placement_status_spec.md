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
  CUDA device `0` implicitly; it uses the backend default tensor allocation
  until a device-aware optimizer-state SFFI is selected.

## Covered Requirement

- Torch device placement must not be user-visible as correct when it is actually
  hardcoded to CUDA device `0`.

## Not Covered

- Live CUDA placement against libtorch.
- Device-preserving optimizer state for parameters already on CUDA.
