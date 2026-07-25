# SYCL Parity + Unified GPU/FPGA Kernel Plan

Date: 2026-06-13
Research: `doc/01_research/language/gpu_fpga/sycl_vs_simple_unified_accelerator_research_2026-06-13.md`
Goal: close all 12 BEHIND gaps (G1–G12) so one Simple kernel programs GPU and
FPGA the same way, while preserving the 7 axes where Simple already beats SYCL.

Exit criterion ("all better"): every scorecard row reads AHEAD or PAR+, with a
spec or fail-closed contract proving each row.

## Wave 1 — std.gpu async + memory model (G2, G3, G4, G10 host-path) — library-level, pure Simple

| Item | Deliverable | Acceptance |
|------|-------------|------------|
| W1.1 Queue/Event | `src/lib/nogc_sync_mut/gpu/queue.spl`: `GpuQueue` (in-order default, `out_of_order()` opt), `GpuEvent`, `submit`, `depends_on`, `wait`; CUDA-stream-backed when available, deterministic CPU fallback otherwise | unit spec passes with no GPU present; CUDA path wired via existing `CudaStream`/`CudaEvent` |
| W1.2 USM trio | `src/lib/nogc_sync_mut/gpu/usm.spl`: `gpu_malloc_device/host/shared(gpu, bytes)` + typed variants; maps to cudaMalloc / pinned host / managed (CUDA), `rt_oneapi_malloc_shared` (oneAPI), heap fallback (None backend) | spec: alloc/copy/free across backend=None deterministically; CUDA path behind `require_cuda` |
| W1.3 Range launch sugar | `gpu_parallel_for(queue, n, kernel_ref, args)` computing grid/block (256 default) with implicit tail guard | spec: launch-shape math (grid/block/tail) unit-tested CPU-side |
| W1.4 Task graph (lite) | `GpuTaskGraph`: record submits + edges, `replay()` (SYCL-graph equivalent); built on W1.1 events | spec: diamond dependency executes in topological order on CPU fallback |

Runtime externs needed (Rust seed additions → require `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` per extern-bootstrap rule): `rt_cuda_malloc_managed`, `rt_cuda_host_alloc`. Until then W1.2 CUDA-shared falls back to device+explicit copy with a recorded TODO.

## Wave 2 — kernel capability parity (G5, G6, G7, G8, G11)

| Item | Deliverable | Acceptance |
|------|-------------|------------|
| W2.1 Descriptive kernels | `parallel fn k(i: idx, ...)` or `@kernel(range)` lowering: compiler injects `idx = block*dim+thread` + bounds guard; keeps `<<<>>>` for prescriptive use | gpu_checker accepts; PTX + OpenCL contracts show injected guard |
| W2.2 Sub-group intrinsics | `gpu_warp_id/lane_id/warp_shuffle(_up/_down/_xor)/warp_ballot` → PTX `shfl.sync`, OpenCL `sub_group_*`, Metal simdgroup | backend contract specs per target; fail-closed on unsupported targets |
| W2.3 Group algorithms | `gpu_block_reduce<T>(op)`, `gpu_block_scan`, `gpu_broadcast` as checker-recognized builtins lowered to shared-mem trees (or W2.2 shuffles) | numeric spec vs CPU reference |
| W2.4 Launch reductions | `gpu_parallel_reduce(queue, n, init, op, kernel)` — two-pass block reduction, library-level over W2.3 | spec: sum/max over 1M elements == CPU result |
| W2.5 Spec constants | `@spec_const val` in kernel modules; PTX/OpenCL recompile-on-set via existing `CudaModuleCache` | contract: constant folded into emitted source |
| W2.6 Kernel vec types | `vec2/4/8<T>` kernel-legal types mapped to native vector types per backend | contract spec per backend |

## Wave 3 — unified FPGA lane (G1, G9) — the headline

| Item | Deliverable | Acceptance |
|------|-------------|------------|
| W3.1 Kernel→VHDL bridge | Route `@gpu_kernel` MIR into VHDL backend: kernel becomes entity; ndrange → counter-driven pipelined loop; `gpu_thread_id_*` → loop counters; `gpu_shared_mem` → BRAM via `vhdl_memory_templates`; `gpu_syncthreads` → stage boundary. Flag: `--gpu-target=vhdl` (alias in `gpu_target_metadata.spl`); flip `vhdl_backend.spl:257` to kernel-aware | same `vector_add` kernel emits PTX, OpenCL C, **and** synthesizable VHDL; GHDL testbench (auto-generated) matches CPU reference |
| W3.2 FPGA attributes | `@unroll(n)`, `@pipeline(ii=n)`, `@memory(banks=n)` decorators (parser already handles decorator list) honored by VHDL lane, ignored-with-note by GPU lanes | contract: attribute → emitted VHDL structure assertions |
| W3.3 Pipes | `GpuPipe<T, depth>` inter-kernel channel: VHDL FIFO template on FPGA; device-global ring buffer on GPU; checker-validated blocking read/write | producer/consumer pair runs in GHDL sim and CUDA |
| W3.4 Board flow | Extend `generate_riscv_fpga_bundle.spl` pattern: `bin/simple build --gpu-target=vhdl --board=kv260` emits Vivado bundle + manifest for kernel lanes | bundle generated; KV260 hardware bring-up tracked separately |

## Wave 4 — runtime polish (G10 device-parity, G12)

| Item | Deliverable | Acceptance |
|------|-------------|------------|
| W4.1 Generic CPU executor | Any `@gpu_kernel` runnable via `gpu_none()` backend: interpreter loop over ndrange (serial), `@simd` lane where shapes allow; makes every kernel testable on CI with no hardware | existing kernel examples pass on CPU backend in CI |
| W4.2 Event profiling | `GpuEvent.elapsed_ms(other)` via cuEventElapsedTime / Vulkan timestamps; queue `enable_profiling()` | spec on CUDA host; CPU fallback returns wall-clock |
| W4.3 Async error model | device-side failures surface as `Result` on `queue.wait()`, not process aborts | spec: OOM alloc → Err, not crash |

## Sequencing and rules

- Wave 1 first (pure library, no compiler changes, immediately spec-testable in
  interpreter — Wave 1 has no bootstrap dependency).
- Waves 2/3 touch compiler MIR/backends: implement in Simple per
  `feedback_fix_spl_not_rust`; new externs require seed bootstrap redeploy.
- Every wave: sspec specs (no skip(), `to_equal(true)` matcher rule), fail-closed
  backend contracts mirroring `opencl_backend_contract_spec.spl`, doc updates to
  `doc/07_guide/compiler/backends/gpu_programming.md`.
- Parallelizable: W2 items are disjoint per-intrinsic-family; W3.1 must precede
  W3.2/W3.3. Use disjoint file scopes per agent (parallel-scope-partition rule).

## Status

- [x] Research + scorecard (this plan's companion doc)
- [x] W1.1 Queue/Event — `src/lib/nogc_sync_mut/gpu/queue.spl` (CPU-deterministic core; CUDA stream binding TODO recorded in-file)
- [x] W1.3 Range launch math — `launch_shape` in queue.spl
- [x] W1.4 Task graph lite — `GpuTaskGraph` in queue.spl
- [x] W1.2 USM trio — `src/lib/nogc_sync_mut/gpu/usm.spl` (None-backend deterministic; CUDA managed/pinned externs = seed work, recorded)
- [x] W2.4 (library layer) — `GpuQueue.parallel_reduce_i64` CPU-deterministic fold; GPU two-pass block reduction still pending behind W2.3
- [x] W2.2 Sub-group intrinsics — gpu_lane_id/warp_id/warp_size, 4 shuffle variants, ballot; PTX (`shfl.sync.*`, `vote.sync.ballot`) + OpenCL (`sub_group_*`) lanes, fail-closed; both `// warp sync` placeholders replaced with `bar.warp.sync`; contract spec 24/24 (`test/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.spl`)
- [x] G3 (library layer) — `GpuAccessGraph` implicit RAW/WAW/WAR DAG from declared buffer access sets
- [x] G4 (device kind) — `usm_malloc_device` CUDA-backed via `rt_cuda_mem_alloc`/`rt_cuda_mem_free`; shared/managed still needs seed externs
- [x] W4.2 (host path) — `GpuEvent.elapsed_nanos`/`elapsed_ms` + `GpuQueue.enable_profiling`; device timers pending native stream binding
- [x] W2.3 Group algorithms — gpu_warp_reduce_add/broadcast/scan_add; OpenCL `sub_group_reduce_add`/`broadcast`/`scan_inclusive_add` + PTX butterfly/idx/up shuffle sequences with predicated adds; contract spec 21/21 (`group_algorithms_contract_spec.spl`); G7 closed at kernel level
- [x] W4.1 Generic CPU executor — `cpu_kernel_run_1d` + state-backed gpu_* index intrinsics in `gpu_ops.spl`; any kernel-shaped body runs a real 1D ndrange on host (serial; shared-mem/syncthreads exchange unsupported, documented); G10 closed for 1D
- [x] W2.5 Spec constants — `gpu_spec_const_i64(name, default)` intrinsic + `SpecConstRegistry` (set/clear/resolve), folded literals in OpenCL + PTX `mov.s64`; 13/13 (`spec_constants_contract_spec.spl`); G8 closed
- [x] W3.2 FPGA attributes — `VhdlKernelAttrs` (unroll_factor / pipeline_ii / memory_banks) shape kernel-entity VHDL (structural unroll, `GENERIC (II ...)`, banked port groups), fail-closed `VHDL-KERNEL-ATTR-INVALID`; 20/20 (`vhdl_kernel_attrs_contract_spec.spl`); G9 closed at backend level. TODO(W3.2-frontend): wire parsed `@unroll`/`@pipeline`/`@memory` decorators into `VhdlKernelAttrs` (v1 passes the options struct explicitly)
- [x] W3.3 Pipes — both halves: `GpuPipe` host FIFO (`src/lib/nogc_sync_mut/gpu/pipe.spl`) + VHDL FIFO entity/endpoints/topology (`vhdl_kernel_pipe.spl`, 44/44 `vhdl_kernel_pipe_contract_spec.spl`)
- [x] W4.3 Error model — `GpuQueue.wait_result() -> Result<i64, text>`, first-failure capture, no aborts
- [x] W2.6 Vec types — gpu_vec4/vec2_load/store_f32 intrinsics; OpenCL `vload4/vstore4/vload2/vstore2` (float4/float2) + PTX `ld/st.global.v4/v2.f32`; 22/22 (`vec_types_contract_spec.spl`); G11 closed
- [ ] W2.1 descriptive kernel lowering — pending (compiler frontend; library `parallel_for`+CPU executor cover the productivity gap meanwhile)
- [ ] W3.4 board flow, G4 shared/managed seed externs, W3.2 frontend decorator wiring — follow-ups
- Found during W1: `grid` named-arg parser bug (P2) — `doc/08_tracking/bug/grid_identifier_named_arg_parse_failure_2026-06-13.md`; API uses grid_dim/block_dim until fixed
- [ ] W3.x — pending (headline)
- [ ] W4.x — pending
