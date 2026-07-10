# GPU Performance Measurement Harness Runtime Blocked - 2026-07-10

## Severity

P1. The local host has NVIDIA CUDA and Vulkan devices, but neither canonical
Simple benchmark path produces usable measured offload evidence.

## Reproduce

```sh
SIMPLE_LIB=src bin/simple run test/05_perf/local_gpu_check/gpu_perf_compare.spl
SIMPLE_LIB=src bin/simple run test/05_perf/local_gpu_check/run_gpu_check.spl
```

## Observed

`gpu_perf_compare.spl` exits `139` immediately after entering its CUDA
`dlopen` SFFI path. `run_gpu_check.spl` builds both C benchmarks but the
self-hosted runtime reports `unknown extern function: rt_exec_output`; it
therefore parses empty output as `unclassified-output` with missing timings.

## Required Fix

Provide one supported process-output facade to standalone performance runners,
or repair the existing `rt_exec_output` runtime symbol. Then require the CUDA
and Vulkan rows to report GPU timing, CPU timing, readback timing, and a
classified overhead verdict before claiming measured GPU acceleration.

## Evidence Rule

Do not accept modeled transfer-pixel economics, empty subprocess output, or
the crashing `dlopen` harness as measured offload evidence.
