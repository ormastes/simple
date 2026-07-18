<!-- codex-architecture -->
# Processing Backend Architecture

**Date:** 2026-06-14
**Status:** Partial — validated `FillU32` vertical slice implemented
**Scope:** Portable compute, draw, tensor, RV64 vector, and FPGA soft-accelerator backend lane.

## Bottom Line

Simple already has the software-side pieces needed to build a portable
processing backend: CUDA and Vulkan runtime hooks, generated GPU examples,
deep-learning tensor paths, RISC-V cross targets, MDSOC architecture structure,
and a conservative VHDL backend. This is not yet a real RISC-V64 Adreno/Mali-like
GPGPU implementation. Treat the current repository as the base for one:

```text
Simple source
  @kernel / @simd / @vulkan_kernel / @draw / @matops
        |
Processing IR
        |
Backends
  Vulkan/SPIR-V       -> Adreno/Mali/desktop GPU
  CUDA                -> NVIDIA
  LLVM RV64GCV        -> RISC-V64 vector CPU / accelerator
  VHDL/RTL            -> FPGA soft-GPGPU / matmul engine
  CPU fallback        -> correctness oracle and tests
```

## Current State

The first runtime-neutral slice now exists. `src/lib/common/processing/processing_ir.spl`
owns a validated `FillU32` value and CPU oracle;
`src/lib/gc_async_mut/processing/vulkan_fill_u32.spl` executes that value through
the existing Vulkan SFFI. Its storage-buffer dispatch shares the Vulkan owner's
fenced tri-state lifecycle with Engine2D: only status `1` permits readback,
status `0` is safe to tear down but ineligible for a receipt, and status `-1`
transfers its uniquely owned buffer, pipeline, and shader to the canonical
Vulkan dependency quarantine while the native runtime retains command/fence
ownership. The owner reaps only after device-idle and gates shutdown until all
releases succeed. The SimpleOS host service accepts the existing bounded
wire command only after Vulkan negotiation, compares device readback with the
CPU oracle, and reports device provenance. This is not yet the compiler MIR
bridge, public `std.processing` API, CUDA/Metal backend, or `simplegpu64`.

| Area | Existing repo evidence | Design consequence |
|------|------------------------|--------------------|
| CUDA/Vulkan runtime | `src/compiler_rust/runtime/src/cuda_runtime.rs`, `src/compiler_rust/runtime/src/value/gpu_vulkan/`, `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` | Reuse runtime handles and fail-closed backend diagnostics. |
| Vulkan compute examples | `src/compiler_rust/lib/std/examples/graphics/vulkan/` | Keep Vulkan/SPIR-V as the first real GPU target. |
| GPU guides | `doc/07_guide/compiler/backends/gpu_programming.md`, `doc/07_guide/lib/gpu_3d/gpu_api.md` | Layer processing below current `std.gpu` and graphics guides. |
| Deep-learning tensors | `doc/07_guide/deep_learning/deep_learning.md`, `src/compiler_rust/runtime/src/value/sffi/pytorch/` | Expose high-level matops above raw kernels. |
| RV64 targets | `doc/04_architecture/hardware/riscv/`, `src/runtime/startup/linux/riscv64/` | Add RV64GCV as a vector backend before soft-GPGPU hardware. |
| VHDL subset | `doc/04_architecture/hardware/vhdl/vhdl_hardware_subset_contract.md` | Start with explicit blocks, not general HLS. |
| MDSOC | `src/compiler/85.mdsoc/`, `doc/04_architecture/compiler/mdsoc/` | Model processing as a capability capsule with strict ownership. |

## To-Be Layer List

```text
src/lib/processing/                         public Simple processing API
src/lib/common/processing/                  runtime-neutral validated IR values and CPU oracles
src/compiler/00.common/processing/          shared IR contracts and diagnostics
src/compiler/50.mir/processing/             MIR-to-ProcessingIR bridge
src/compiler/70.backend/backend/processing/ backend selection and lowering
src/compiler/70.backend/backend/processing/vulkan/
src/compiler/70.backend/backend/processing/cuda/
src/compiler/70.backend/backend/processing/rv64/
src/compiler/70.backend/backend/processing/vhdl/
src/runtime/processing/                     CPU/Vulkan/CUDA/device scheduling
src/os/driver/gpu/simplegpu/                MMIO, queues, DMA, fences
src/hw/simplegpu64/                         RTL/VHDL soft-GPGPU blocks
```

Tree-private ownership is the default. Common processing contracts belong under
`src/compiler/00.common/processing/`. Backends may consume the common IR but must
not depend on each other's private lowering internals.

## Processing API Shape

The core abstraction is a processing device, not a vendor GPU:

```simple
val dev = processing.Device.select(
    kind: "auto",
    prefer: ["vulkan", "simplegpu", "cuda", "rv64v", "cpu"]
)

val q = dev.queue()
val a = dev.buffer<f16>(m * k)
val b = dev.buffer<f16>(k * n)
val c = dev.buffer<f16>(m * n)

q.upload(a, host_a)
q.upload(b, host_b)
q.dispatch(matmul_tile, grid: (ceil(m, 16), ceil(n, 16), 1),
    local: (16, 16, 1), args: (a, b, c, m, n, k))
q.download(c, host_c)
q.wait()
```

## Processing IR Contract

ProcessingIR is separate from ordinary MIR and only accepts GPU-safe operations:

- Kernel metadata: grid, local size, subgroup size, arguments, resources.
- Memory operations: global, local, constant, image, and DMA copy.
- Control: `if`, static loops, barriers, subgroup barriers, predicated select.
- Math: integer ops, f32/f16/bf16 add/mul/fma, dot, MMA, approximate functions.
- Draw: fill, line, triangle, blend, tile store.
- Tensor: GEMM, conv2d, softmax, layernorm, attention, reduce, scan.

Reject heap allocation, GC, unbounded loops, virtual dispatch, closures, host
pointers, exceptions, ordinary async, unknown aliasing, and recursion. This
matches the current VHDL policy: explicit subset, explicit diagnostics, and no
hidden runtime lowering.

## simplegpu64 Capsule

```text
simplegpu64
  host: MMIO, command ring, descriptor tables, DMA, later IOMMU
  command: RV64IMAC control core, queue scheduler, fences, context state
  clusters: SIMT front end, warp scheduler, scalar lane, vector ALUs
  math: FP32, FP16, BF16, INT8/INT4 dot, tensor/MMA tile unit
  memory: local SRAM, L1 per cluster, shared L2, coalescer, global DMA
  draw: tile binning, triangle setup, raster, blend/writeback
  debug: counters, trace buffer, queue timeline, kernel event records
```

Do not build a normal RV64 CPU and call it a GPU. Use RV64 for command/control
and add SIMT, tensor, tile-local SRAM, barriers, atomics, and coalesced memory
around it. Adreno and Mali are inspiration for tile rendering and unified
shader/compute clusters; Vulkan/SPIR-V remains the compatibility path for real
mobile and desktop GPUs.

## MDSOC Visibility Matrix

| Raw layer | Common processing node | Public to parent | Public to next layer |
|-----------|------------------------|------------------|----------------------|
| `src/lib/processing` | Device, buffer, queue, fence, kernel handles | `std.processing.*` | Compiler sees typed kernel/resource metadata only. |
| `src/compiler/50.mir/processing` | ProcessingIR builder diagnostics | MIR bridge APIs | Backend sees validated ProcessingIR only. |
| `src/compiler/70.backend/backend/processing` | Backend capability records | Processing backend facade | Runtime sees compiled artifact descriptors only. |
| `src/runtime/processing` | Device events and memory handles | Runtime facade | Driver sees MMIO/DMA packets only. |
| `src/os/driver/gpu/simplegpu` | Queue packet ABI | Driver capsule | Hardware sees packet/register ABI only. |
| `src/hw/simplegpu64` | RTL entity contracts | Simulation and synthesis targets | No upward source dependency. |

## Build Stages

1. Define ProcessingIR plus CPU golden backend. (`FillU32` runtime slice done;
   compiler lowering remains.)
2. Lower `@kernel` and `@vulkan_kernel` to Vulkan/SPIR-V.
3. Add `std.processing` buffers, queues, fences, and events.
4. Add matops: tiled GEMM, reduce, softmax, layernorm.
5. Add draw primitives: fill, line, rect, blend, image blur.
6. Add LLVM RV64GCV vector backend.
7. Add fixed-function VHDL GEMM/reduce/blend blocks.
8. Add full `simplegpu64` SIMT soft-GPGPU after software behavior is stable.

## Acceptance Lane

Start with small deterministic tests:

- `vector_add`
- `saxpy`
- `reduce_sum`
- `matmul_tile`
- `image_blur`
- `fill_rect`
- `alpha_blend`

Every hardware feature must have a CPU oracle and a Vulkan or RV64 software
counterpart before FPGA or SIMT lowering is treated as complete.
