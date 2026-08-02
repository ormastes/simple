<!-- codex-architecture -->
# Processing Backend TLDR

Simple now has shared `FillU32` and stride-aware, half-open `FillRectU32`
semantics, CPU oracles, Vulkan/CUDA/Metal artifact owners, and typed compile and
device-readback evidence. A focused Vulkan test compiles a fixed representative
rectangle through the Simple MIR Vulkan backend, validates its SPIR-V with
`spirv-val`, submits it to a physical Vulkan device, and compares raw readback.
The public processing device/queue API and general dynamic drawing lowering
remain open.

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

Artifact cache identity includes every operation, target, value, extent,
stride, and rectangle coordinate. Compiler/validator/driver/device changes also
invalidate native material. Cache immutable source/binary only; buffers,
pipelines, fences, handles, and readback authority remain transient owners.
Startup probes do not prove execution. The hot path requires native submission,
known completion, positive device identity, typed device readback, and exact
oracle parity. CPU fallback, missing validation, and unsupported semantics fail
closed.

Targets: warm artifact selection under 1 ms and less than 4 MiB added
steady-state RSS excluding driver allocations. Compiler and validator processes
are cold-path only; no hot request may scan the repository or invoke them.

First stages: CPU golden backend, Vulkan/SPIR-V lowering, processing buffers and
queues, tiled matops, draw primitives, RV64GCV, fixed VHDL blocks, then SIMT
`simplegpu64`.

Reject heap allocation, GC, unbounded loops, host pointers, ordinary async, and
general HLS. Every hardware feature needs a CPU oracle and software backend
evidence first.
