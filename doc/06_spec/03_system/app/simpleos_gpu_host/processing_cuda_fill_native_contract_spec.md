# Direct CUDA ProcessingIR Fill Contract

## Purpose

Prove that `processing_ir_execute_cuda` executes the shared 64-element
`FillU32(0x01020304)` fixture on a CUDA device without CPU fallback.

## Run

Build `src/app/test/processing_cuda_fill_probe.spl` incrementally against the
CUDA-enabled runtime, then run:

```sh
sh scripts/check/check-processing-cuda-fill-native.shs
```

## Checks

1. All 64 values exactly match `0x01020304`.
2. Expected and actual checksums equal `1082179840`.
3. Mismatch count is zero.
4. Device handle and identity are positive.
5. The receipt names CUDA device readback and rejects CPU fallback.

## Current Evidence

The source contract passes. The incrementally built native probe now uses
length-tracked PTX and kernel-name ABIs, loads and launches CUDA successfully,
and reaches device readback. Its 64-value checksum is eight times the expected
checksum, all 64 values mismatch, and the native identity is negative despite
the runtime's positive-identity contract. The live wrapper correctly fails. See
`processing_ir_cuda_vulkan_fill64_parity_2026-07-26.md`.
