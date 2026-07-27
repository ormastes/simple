# Direct CUDA ProcessingIR Fill Contract

## Purpose

Prove that `processing_ir_execute_cuda` executes the shared
`FillU32(0x01020304)` fixture on a CUDA device without CPU fallback. The
default parity mode uses 64 elements; large mode uses the calibrated
1,048,576-element policy threshold.

## Run

Build `src/app/test/processing_cuda_fill_probe.spl` incrementally against the
CUDA-enabled runtime, then run:

```sh
sh scripts/check/check-processing-cuda-fill-native.shs
```

Run the threshold workload against the same candidate:

```sh
PROCESSING_CUDA_FILL_MODE=large \
  sh scripts/check/check-processing-cuda-fill-native.shs
```

## Checks

1. Every returned value exactly matches `0x01020304`.
2. Expected and actual checksums equal `1082179840` in parity mode or
   `17730434498560` in large mode.
3. Mismatch count is zero.
4. Device handle and identity are positive.
5. End-to-end executor time is positive.
6. The receipt names CUDA device readback and rejects CPU fallback.
7. Readback materialization uses the runtime-owned bulk
   `rt_u32s_from_raw` conversion, not a per-element `push` loop.

## Current Evidence

The retained native candidate passes both modes with exact checksums, zero
mismatches, positive handle/identity, device readback, and no CPU fallback.
The 1,048,576-element run improved from `1044501 us` with per-element
materialization to `593323 us` with the canonical bulk converter. This is
retained-candidate evidence, not source-matched compiler freshness. Persistent
CUDA context/module ownership remains required to remove cold setup cost.
