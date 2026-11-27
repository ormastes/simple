# GPU Performance Measurement Harness Runtime Blocked - 2026-07-10
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Triage note 2026-11-25 (p2w2-aj)

**Disposition: SKIP — hardware + full-bootstrap deployment required, not
bounded for this lane.** The unblock condition is a successful self-hosted
(stage-4) build deployed to `bin/release/<triple>/simple` and re-run of the
CUDA/Vulkan benchmark harness on a GPU host. Neither is possible here: this
lane is forbidden from running bootstrap/cargo builds, the host's pinned
`bin/simple.exe` is the v1.0.0-rc.1 Rust seed which also fails repo-wide spec
runs at HEAD (`unknown decorator '@representation_boundary'`, cfd89933699),
and the benchmark requires live NVIDIA CUDA/Vulkan devices plus a compiler
build whose 2026-07 deployment attempt timed out on parser errors.

Partial-fix claim re-checked by code inspection on release/1.0.0 HEAD:
`rt_exec_output` IS exported by the runtime
(`src/compiler_rust/runtime/src/value/cli_sffi.rs:872`, twin
`src/runtime/runtime_native.c:19756`) and routed for codegen
(`src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:88` prefix rule).
The harness files (`test/05_perf/local_gpu_check/gpu_perf_compare.spl`,
`run_gpu_check.spl`) are unchanged in tree. The per-record Evidence Rule
stands: the diagnostic-runtime CUDA/Vulkan numbers are not release evidence
until a deployed self-hosted binary re-measures them. Header status (open,
owner triage) is accurate; remains OPEN for a bootstrap-capable GPU lane.
