# Direct CUDA ProcessingIR Fill Contract

## Purpose

Prove that `processing_ir_execute_cuda` executes the shared
`FillU32(0x01020304)` fixture on a CUDA device without CPU fallback. The
default parity mode uses 64 elements; large mode uses the calibrated
1,048,576-element policy threshold. Warm mode executes that threshold twice
through one retained `CudaSession`.

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

Run the retained-session timing check:

```sh
PROCESSING_CUDA_FILL_MODE=warm \
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
8. Warm mode requires the second exact device request to complete faster than
   the cold request through the same executor.

## Current Evidence

The retained native candidate passes both modes with exact checksums, zero
mismatches, positive handle/identity, device readback, and no CPU fallback.
The 1,048,576-element run improved from `1044501 us` with per-element
materialization to `593323 us` with the canonical bulk converter. The retained
session run completed cold in `861499 us` and warm in `69331 us`, a 12.4x
improvement, with exact values and unchanged device provenance. Those timings
precede the subsequent retained-context activation repair; its two-context
runtime test passes, but the capped Simple probe was not rebuilt a fourth time.
Correlated daemon-wire and multi-sample evidence remain open.
