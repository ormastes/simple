# Processing Backend Guide

**Status:** Partial — `FillU32` CPU/Vulkan slice available

The processing backend is the planned portable compute layer underneath
`std.gpu`, draw APIs, and ML matops. It should use the current CUDA/Vulkan
runtime hooks, RISC-V cross targets, and conservative VHDL backend without
pretending that the repository already contains a full RISC-V64 mobile-style
GPGPU.

## Available Today

`std.common.processing.processing_ir` provides the validated `FillU32` IR value
and CPU oracle. `std.gc_async_mut.processing.vulkan_fill_u32` executes it through
the existing Vulkan SFFI and returns device-read bytes. The SimpleOS QEMU host
service negotiates this as Vulkan processing and requires exact CPU parity.
Fresh x86_64, AArch64, and RV64 QEMU probes report checksum `1792` with zero
mismatches for 256 elements filled with `7`. CUDA, Metal, compiler kernel
lowering, and a public device/queue API remain unavailable.

Vulkan ProcessingIR promotes a receipt only after the shared SFFI owner proves
fenced completion and dependency release. A known-safe but ineligible result is
torn down without readback; unknown completion retains dependent resources and
the device. The canonical Vulkan SFFI owner serializes and deduplicates those
transfers, reaps them only after device-idle, and refuses shutdown while a
dependency remains unreleased. Submitted commands and fences stay exclusively
owned by the native runtime; a provably unsubmitted command whose discard
failed remains in the Simple owner until discard can be retried safely.

## Target Stack

```text
Simple source
  @kernel / @simd / @vulkan_kernel / @draw / @matops
        |
ProcessingIR
        |
CPU reference | Vulkan/SPIR-V | CUDA | LLVM RV64GCV | VHDL/RTL | simplegpu64
```

Use CPU first as the correctness oracle. Use Vulkan/SPIR-V first for real
Adreno, Mali, and desktop GPUs. Use RV64GCV for vector CPU or accelerator mode.
Use VHDL/RTL only for explicit hardware blocks such as GEMM, reductions, DMA,
queues, and blending.

## API Direction

Prefer a device-neutral API:

```simple
val dev = processing.Device.select(
    kind: "auto",
    prefer: ["vulkan", "simplegpu", "cuda", "rv64v", "cpu"]
)
val q = dev.queue()
val a = dev.buffer<f16>(m * k)
val b = dev.buffer<f16>(k * n)
val c = dev.buffer<f16>(m * n)
q.dispatch(matmul_tile, grid: (ceil(m, 16), ceil(n, 16), 1),
    local: (16, 16, 1), args: (a, b, c, m, n, k))
q.wait()
```

## Kernel Subset

Processing kernels may use explicit buffers, local/tile memory, static loops,
barriers, subgroup operations, fixed-shape math, draw primitives, and tensor
ops. They must reject heap allocation, GC, unbounded loops, host pointers,
closures, virtual dispatch, exceptions, ordinary async, unknown aliasing, and
unsupported recursion.

## Implementation Order

1. ProcessingIR and CPU golden backend. (`FillU32` runtime slice complete.)
2. Vulkan/SPIR-V lowering for `@kernel` and `@vulkan_kernel`.
3. `std.processing` device, buffer, queue, fence, and event APIs.
4. Matops: GEMM, reduce, softmax, layernorm, attention.
5. Draw compute primitives: fill, line, rect, blend, image blur.
6. LLVM RV64GCV lowering.
7. VHDL fixed-function blocks for GEMM, reduce, blend, queue, and DMA.
8. `simplegpu64` SIMT soft-GPGPU.

## Verification

Every new backend lane needs the same golden scenarios:

- vector add
- saxpy
- reduction
- tiled matmul
- image blur
- fill rect
- alpha blend

Hardware work is not complete until CPU oracle output, software backend output,
and RTL/simulation output agree for the same inputs.

Architecture: `doc/04_architecture/compiler/backend/processing_backend.md`.
