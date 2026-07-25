<!-- codex-architecture -->
# Processing Backend TLDR

Simple now has one real portable slice: validated ProcessingIR `FillU32`, a CPU
oracle, and Vulkan device execution/readback used by the SimpleOS QEMU host
service. It still does not have compiler kernel lowering, CUDA/Metal ProcessingIR
backends, a public processing API, or a real RV64 Adreno/Mali-like GPGPU.

Vulkan compute dispatch is fenced and tri-state in the canonical SFFI owner.
ProcessingIR reads only status `1`; unknown completion retains dependencies
rather than risking teardown while work may still be in flight.

```text
Simple @kernel/@draw/@matops
  -> ProcessingIR
  -> CPU oracle, Vulkan/SPIR-V, CUDA, RV64GCV, VHDL/RTL, simplegpu64
```

Core decision: make `processing.Device` the abstraction, not vendor-specific
CUDA/Vulkan names. Keep `std.gpu`, draw, and ML APIs above it.

Important boundaries:

- `src/compiler/00.common/processing/` owns shared IR contracts.
- `src/lib/common/processing/` owns runtime-neutral values and CPU oracles.
- `src/compiler/70.backend/backend/processing/` owns lowering selection.
- `src/runtime/processing/` owns queues, memory handles, events, and fallback.
- `src/os/driver/gpu/simplegpu/` owns MMIO, DMA, command queues, and fences.
- `src/hw/simplegpu64/` owns RTL/VHDL.

First stages: CPU golden backend, Vulkan/SPIR-V lowering, processing buffers and
queues, tiled matops, draw primitives, RV64GCV, fixed VHDL blocks, then SIMT
`simplegpu64`.

Reject heap allocation, GC, unbounded loops, host pointers, ordinary async, and
general HLS. Every hardware feature needs a CPU oracle and software backend
evidence first.
