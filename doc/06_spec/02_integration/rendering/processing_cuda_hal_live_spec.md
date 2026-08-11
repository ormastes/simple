# Physical CUDA HAL ProcessingIR Transport

## Purpose

Prove the Simple interpreter/runtime CUDA HAL reaches a physical NVIDIA driver
without relying on the blocked native-build worker. The scenario uses CPU input
upload, repository Simple `CudaSession`, PTX dispatch, raw device download, and
exact CPU-oracle comparison. `nvcc` availability alone is not evidence.

## Required evidence

1. CUDA session initialization and context activation return success.
2. Runtime device identity and loaded PTX module handles are positive.
3. CPU input `[1, 2, 10, 100]` uploads to device memory.
4. The PTX kernel adds seven on-device and raw download equals
   `[8, 9, 17, 107]` exactly.
5. Two dispatch/download iterations preserve device identity and module handle.
6. Null-destination upload and null-source download both reject rather than
   reporting success.
7. All host/device allocations and the session are released.

The passing run emits three independent machine receipts:

- `PROCESSING_CUDA_HAL_HAPPY` records CUDA device origin, CPU upload, PTX
  dispatch, device download, exact output `8,9,17,107`, positive
  identity/context/module handles, and `cpu_fallback=false`.
- `PROCESSING_CUDA_HAL_REPEAT` records two dispatches with stable device
  identity and module handle.
- `PROCESSING_CUDA_HAL_ERROR` records invalid upload and download status `-1`,
  the canonical `CUDA_ERROR_INVALID_VALUE`, with fail-closed behavior.

## Run

```sh
SIMPLE_LIB=src bin/simple test test/02_integration/rendering/processing_cuda_hal_live_spec.spl --mode=interpreter
```

A PASS is physical CUDA HAL evidence only when all assertions execute against
the runtime driver and raw device readback. CPU mirrors, PTX text inspection,
or compiler availability are insufficient.
