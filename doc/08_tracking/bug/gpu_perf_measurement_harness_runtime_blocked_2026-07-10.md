# GPU Performance Measurement Harness Runtime Blocked - 2026-07-10

**Status:** PARTIAL — rt_exec_output export FIXED (per record); CUDA dlopen SIGSEGV path CLOSED-STALE (2026-09-12: not re-verifiable from the record)

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

## Triage 2026-09-12
The record's own "Fix Status" section already shows `rt_exec_output` fixed with measured CUDA-vs-CPU timings. The separate CUDA `dlopen` SFFI SIGSEGV (exit 139) symptom has no cheap repro re-run in this pass and is older than 45 days; closing that portion per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
