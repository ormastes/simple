# SYCL vs Simple — Unified GPU/FPGA Programming Research

Date: 2026-06-13
Domain: language / gpu_fpga
Companion plan: `doc/03_plan/language/gpu_fpga/sycl_parity_unified_kernel_plan_2026-06-13.md`

## 1. Goal

Evaluate Simple's GPU/FPGA programming model against SYCL 2020 (Khronos, rev 11),
identify every axis where Simple is behind, every axis where Simple is already
ahead, and feed a plan that closes all "behind" items so that Simple GPU and
FPGA can be programmed the same way — and in most ways better than SYCL.

## 2. What SYCL is (grounded summary)

SYCL is an open, royalty-free C++ single-source abstraction for heterogeneous
offload (CPU, GPU, FPGA) layered over backends such as OpenCL, CUDA, HIP, and
Level Zero. Sources: khronos.org/sycl (indexed as `khronos-sycl-overview`),
ENCCS SYCL workshop (indexed as `sycl-feature-tutorial`).

SYCL 2020's feature pillars:

| # | Pillar | Mechanism |
|---|--------|-----------|
| S1 | Single source host+device | C++ lambdas compiled per-target; one TU targets CPU/GPU/FPGA |
| S2 | Device discovery/selection | platforms, devices, device selectors |
| S3 | Queues + events | in-order and out-of-order `queue`, `event`, `depends_on` |
| S4 | Implicit data-dependency DAG | `buffer` + `accessor` build a task graph automatically |
| S5 | USM | `malloc_device` / `malloc_host` / `malloc_shared` pointer model |
| S6 | Descriptive kernels | `parallel_for(range)` with implicit bounds, `nd_range` with work-groups |
| S7 | Group algorithms | `reduce_over_group`, scans, broadcasts, sub-group (warp) shuffles |
| S8 | Built-in reductions | `sycl::reduction` objects passed to `parallel_for` |
| S9 | Specialization constants | late-bound constants folded at kernel JIT time |
| S10 | FPGA path | Intel oneAPI HLS flow; pipes, `[[intel::initiation_interval]]`, unroll, memory banking |
| S11 | CPU/host fallback | every kernel runs on the CPU device |
| S12 | Vector/math types | `vec<T,N>`, swizzles, device math builtins |
| S13 | Profiling/error model | event profiling, async exception handlers |

SYCL's structural weaknesses (opportunities for Simple to be better):
- Template-heavy C++: slow compiles, notoriously poor diagnostics; device-code
  restriction violations surface as late template/link errors.
- FPGA support is effectively a single closed vendor flow (Intel/Altera HLS).
  No readable RTL output, hours-long synthesis for any iteration, no testbench
  generation, no provenance.
- No language-level kernel-subset enforcement; no integrated test framework;
  performance portability explicitly not guaranteed.
- Buffers/accessors are verbose; USM reintroduces unchecked data races.

## 3. Simple's current accelerator surface (verified 2026-06-13)

Language:
- `@gpu` / `@gpu_kernel` / `kernel fn` markers (`parser_types.spl:85`,
  `attributes_part1.spl:529`), CUDA-style launch syntax `k<<<grid, block>>>(args)`
  (`lexer_types.spl:144 TripleLess`).
- Compile-time kernel constraint checker `35.semantics/gpu_checker.spl`:
  rejects heap alloc, closures, recursion, dyn dispatch, I/O, async, exceptions
  inside kernels — before codegen.
- `@simd`, `@bounds` attributes; `gpu_target_metadata.spl` target aliases.

Backends (`src/compiler/70.backend/`):
- PTX builder (`backend/cuda/ptx_builder.spl`), CUDA backend + launcher.
- OpenCL backend with fail-closed contract (807 lines, reference contract spec).
- `gpu_portable_compute.spl`: one kernel emitted as CUDA, HIP, OpenCL C, or
  Metal Shading Language from shared MIR — no per-backend duplication.
- VHDL backend (`backend/vhdl/*`, 28+ modules): VHDL-2008 emission, type mapper,
  DSP/memory templates, CDC primitives, register files, testbench generation,
  GHDL smoke gates (RV32+RV64 lanes pass), Vivado bundle generation with
  provenance manifests, KV260 board support (`src/lib/hardware/fpga_k26/`).

Library (`src/lib/nogc_sync_mut/`):
- `gpu/`: `GpuBackend` (Cuda, Vulkan, Rocm, OneApi, Metal, None), `Gpu` device
  handle, `detect_backends`, `GpuArray<T>` typed arrays, `Context`.
- `cuda/`: SFFI + sessions + module cache; cuBLAS L1/L3; streams + events.
- `gpu/engine2d|engine3d`: sessions for CUDA/Vulkan/OpenCL/ROCm/Intel/Metal/
  WebGPU/CPU-SIMD.
- `torch/`: tensor ops, optimizers, training; `io/oneapi_sffi.spl` has
  `rt_oneapi_malloc_shared` (stub-level).
- Testing: `gpu_helpers.spl` (`require_gpu`, `gpu_benchmark`, float tolerance
  asserts) wired into sspec.

GPU intrinsics in kernels: `gpu_thread_id_x/y/z`, `gpu_block_id_*`,
`gpu_block_dim_*`, `gpu_grid_dim_*`, `gpu_syncthreads`, `gpu_shared_mem<T>`,
atomics.

## 4. Scorecard — Simple vs SYCL

Legend: **AHEAD** = Simple better today; **PAR** = rough parity; **BEHIND** = gap to close.

| Axis | SYCL | Simple today | Verdict |
|------|------|--------------|---------|
| Kernel subset diagnostics | late template errors | dedicated semantic checker, early errors | **AHEAD** |
| Multi-vendor source emission | per-backend compilers | one MIR → CUDA/HIP/OpenCL/Metal + PTX | **AHEAD** |
| FPGA transparency | closed HLS, no RTL | open VHDL-2008 + testbenches + provenance + GHDL sim | **AHEAD** |
| Launch ergonomics | queue+lambda boilerplate | native `<<<grid, block>>>` | **AHEAD** |
| Compile speed / error quality | C++ templates | no templates, simple generics | **AHEAD** |
| Integrated testing/benchmark | none in spec | sspec + gpu_helpers + fail-closed contracts | **AHEAD** |
| ML stack integration | external (oneMKL etc.) | std.torch, cuBLAS, engines in-tree | **AHEAD** |
| Device discovery | S2 selectors | detect_backends/preferred_backend (6 backends) | **PAR** |
| Streams/events (raw) | S3 partial | CudaStream/CudaEvent (CUDA-only, low-level) | **PAR−** |
| S1 single source GPU+**FPGA** | one kernel → CPU/GPU/FPGA | `@gpu_kernel` does NOT reach VHDL lane (`vhdl_backend.spl:257` `is_kernel: false`); FPGA lane is whole-module `--backend=vhdl` | **BEHIND (G1, P0)** |
| S3 unified queue/event + depends_on | yes | no `std.gpu` Queue/Event; no cross-backend async model | **BEHIND (G2)** |
| S4 implicit data-dependency DAG | buffers+accessors | manual copies only | **BEHIND (G3)** |
| S5 USM (device/host/shared) | yes | no unified API; oneapi stub only; no CUDA managed mem | **BEHIND (G4)** |
| S6 descriptive `parallel_for(range)` | implicit bounds, nd_range | prescriptive intrinsics only; manual bounds-check idiom | **BEHIND (G5)** |
| S7 group algorithms + sub-group ops | yes | none (only block-level `gpu_syncthreads`; "warp sync" is an emitted comment) | **BEHIND (G6)** |
| S8 built-in reductions | yes | none (manual shared-mem tree) | **BEHIND (G7)** |
| S9 specialization constants | yes | none | **BEHIND (G8)** |
| S10 FPGA kernel tuning (pipes, II, unroll, banking) | yes | VHDL templates exist but not exposed as kernel attributes | **BEHIND (G9)** |
| S11 CPU fallback for kernels | every kernel | engine2d-only CPU-SIMD sessions; no generic kernel-fn CPU executor | **BEHIND (G10)** |
| S12 vec types in kernels | vec<T,N>, swizzles | @simd exists; no kernel vec type surface | **BEHIND (G11)** |
| S13 profiling + async error model | event timing, handlers | gpu_benchmark host-side only; no device event timing API | **BEHIND (G12)** |

Summary: 7 AHEAD, 2 PAR, 12 BEHIND (G1–G12). The single biggest structural gap
is G1: SYCL's headline claim — the *same kernel* runs on GPU and FPGA — is the
one thing Simple's two mature lanes (GPU MIR backends, VHDL backend) do not yet
do together, even though both lanes individually exceed SYCL's equivalents in
transparency.

## 5. Strategic read

Simple does not need to clone SYCL's buffer/accessor C++ API. It needs the
*capabilities* with Simple-native ergonomics:

1. **Unify the lanes (G1+G9)** — route `@gpu_kernel`/`kernel fn` MIR into the
   existing VHDL backend as a kernel-entity lane (ndrange → pipelined loop,
   `gpu_shared_mem` → BRAM template, `gpu_syncthreads` → pipeline stage barrier).
   All emission infrastructure already exists; the missing piece is the bridge
   plus FPGA attributes (`@unroll(n)`, `@pipeline(ii=n)`, `@memory(banks=n)`,
   pipes). This makes Simple the only language with one kernel → PTX + OpenCL +
   Metal + readable VHDL, beating SYCL's closed single-vendor FPGA story.
2. **Async/data model (G2+G3+G4)** — `std.gpu` Queue/Event with `depends_on`,
   USM trio (`gpu_malloc_device/host/shared`) mapped per-backend, and a
   lightweight task-graph layer; checker-enforced safety where SYCL has none.
3. **Kernel capability (G5–G8, G11)** — `parallel_for`-style descriptive launch
   with implicit bounds guard, warp/sub-group intrinsics + group reduce/scan,
   launch-level reduction arguments, spec constants, kernel vec types.
4. **Runtime parity (G10, G12)** — generic CPU executor for any kernel fn
   (serial + SIMD), event-based profiling, async error propagation.

Each closure should land with sspec coverage and fail-closed backend contracts,
preserving the axes where Simple already leads.

## 5a. Status update — gap closures landed 2026-06-13 (same day)

Implementation of the companion plan closed the BEHIND rows as follows (every
closure has a green spec; counts are per-example, re-verified independently of
the implementing agent):

| Gap | Closure | Evidence |
|-----|---------|----------|
| G1 single source GPU+FPGA | `@gpu_kernel` MIR → VHDL entity lane (counter-driven loop process, fail-closed subset) | `vhdl_kernel_entity_contract_spec.spl` 14/14 |
| G2 queue/event | `GpuQueue`/`GpuEvent`, `submit_after` deps fail-closed | `gpu_queue_usm_spec.spl` |
| G3 implicit DAG | `GpuAccessGraph` RAW/WAW/WAR derivation from access sets | same spec |
| G4 USM | trio API; device kind CUDA-backed (`rt_cuda_mem_alloc`); shared/managed = seed-extern follow-up | same spec |
| G5 descriptive parallel_for | library `parallel_for` with implicit bounds + `cpu_kernel_run_1d`; compiler kernel-form (W2.1) still pending | same spec |
| G6 sub-group ops | 8 intrinsics, PTX `shfl.sync.*`/`vote.sync.ballot` + OpenCL `sub_group_*`; warp-sync comment placeholders removed | `subgroup_intrinsics_contract_spec.spl` 24/24 |
| G7 group algorithms | warp reduce_add/broadcast/scan_add (PTX butterfly/idx/up sequences, OpenCL `sub_group_reduce_add` etc.) + launch-level `parallel_reduce_i64` | `group_algorithms_contract_spec.spl` 21/21 |
| G8 spec constants | `gpu_spec_const_i64` + `SpecConstRegistry`, folded at emission | `spec_constants_contract_spec.spl` 13/13 |
| G9 FPGA tuning | `VhdlKernelAttrs` unroll/II/banking + pipes (VHDL FIFO/endpoints/topology + `GpuPipe` host half) | `vhdl_kernel_attrs_contract_spec.spl` 20/20, `vhdl_kernel_pipe_contract_spec.spl` 44/44 |
| G10 CPU fallback | `cpu_kernel_run_1d` + state-backed index intrinsics (1D, serial; no cross-thread shared-mem exchange) | `gpu_queue_usm_spec.spl` |
| G11 vec types | vec2/vec4 f32 load/store intrinsics (vloadN/vstoreN, `ld/st.global.vN.f32`) | `vec_types_contract_spec.spl` 22/22 |
| G12 profiling/errors | `enable_profiling` + `elapsed_ms`, `wait_result() -> Result` | `gpu_queue_usm_spec.spl` |

Residual follow-ups (tracked in plan Status): W2.1 compiler-side descriptive
kernel lowering, W3.2 frontend decorator wiring, W3.4 board bundle flow, G4
shared/managed seed externs, GHDL-simulated end-to-end kernel testbench.
Language bugs found and recorded during the work:
`grid_identifier_named_arg_parse_failure_2026-06-13.md`,
`dict_struct_key_iteration_single_entry_2026-06-13.md`.

## 6. Sources

- khronos.org/sycl — indexed `khronos-sycl-overview` (SYCL 2020 rev 11, UXL/oneAPI ecosystem)
- ENCCS SYCL workshop — indexed `sycl-feature-tutorial` (prescriptive vs descriptive parallelism, SAXPY comparison)
- Repo evidence: paths cited inline; probes run 2026-06-13 (`is_kernel: false` at `src/compiler/70.backend/backend/vhdl_backend.spl:257`; no subgroup/USM/pipe/spec-const hits outside noted stubs).
