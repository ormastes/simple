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

## Fix Status

The runtime now exports and interpreter-registers `rt_exec_output`. A rebuilt
diagnostic runtime produced CUDA `0.02 ms` versus CPU `0.77 ms` for the 1080p
clear (`38.5x`, measured-gpu-faster), while Vulkan reported `2.70 ms` and was
classified measured-gpu-slower-overhead. The normal self-hosted binary still
needs deployment before this is release evidence.

## Deployment Attempt

`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy`
rebuilt the Rust seed, but the self-hosted stage-4 native build did not produce
`bin/release/x86_64-unknown-linux-gnu/simple`. It reported parser errors in
`src/compiler/mir_opt/mir_opt/outline.spl`, `gvn.spl`, and
`src/compiler/hir/hir_lowering/_Items/declaration_lowering.spl`, then timed out
after 7200 seconds. Repair that compiler build before rerunning the deployed
benchmark; the diagnostic-runtime numbers above are not release evidence.

## Evidence Rule

Do not accept modeled transfer-pixel economics, empty subprocess output, or
the crashing `dlopen` harness as measured offload evidence.
