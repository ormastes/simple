<!-- codex-design -->
# SimpleOS Memory Leveling Architecture

Status: selected design for `A + 1 + 1B`.

## Pattern

Use a small policy capsule in `src/os/kernel/memory/memory_leveling.spl`.
The capsule is pure data logic: profiles, page states, capability summaries,
and migration decisions. VMM, swap, GPU, NIC, and DMA drivers remain owners of
their real hardware work.

## Layers

- Simple language model: `std.memory_leveling` represents existing `T`,
  `mut T`, `iso T`, and device-handle ownership as pure placement intent.
- SimpleOS memory policy: selected slice added here; decides `keep`,
  `swap_out`, `promote_cpu`, `demote_cold`, `pin_device`, or `reject`.
- VMM/swap/device drivers: future integration layer; this slice does not move
  real pages.

## Language/OS Boundary

`src/lib/nogc_sync_mut/memory_leveling.spl` is platform-neutral. It exports
intent records and helpers only. `src/os/kernel/memory/memory_leveling.spl`
owns the adapter from language intent to OS page state.

Hardware intent fields are data only. The OS policy accepts real x86/ARM/RISC-V
CPU targets when the intent carries real evidence, and rejects model-only
hardware claims. Vulkan, Metal, CUDA, and RDMA targets are recognized as real
device memory classes but remain pinned/fail-closed until the owner driver
supplies migration, coherence, or deregistration proof.

Vulkan, Metal, and CUDA readback proof upgrades the decision from `reject` to
`pin_device`: the allocation is proven device-readable, but still not movable.
Only Vulkan and CUDA readback-backed pinning are exercised by this lane's
executable spec; Metal shares the same policy path without runtime test evidence.

## Profiles

- `baremetal_static`: no swap, no migration, no GPU/NIC tiers, DMA pin safety
  enabled.
- `simpleos_default`: swap and migration enabled for ordinary CPU pages only.
- `heterogeneous_device`: swap, migration, GPU tier, NIC tier, DMA pin safety,
  and shadow copies enabled.

## Safety Rules

- DMA-pinned pages reject swap and demotion.
- NIC-registered pages reject swap and demotion.
- GPU-resident pages reject swap and demotion until a coherence proof exists.
- Vulkan, Metal, CUDA, and RDMA hardware intents reject movement by default.
- Vulkan, Metal, and CUDA readback-backed intents pin device memory.
- Unknown/external states reject movement.
- Bare-metal profile always keeps pages unless a device pin forces rejection.

## MDSOC Notes

This is a virtual capsule over memory/device boundaries. The public next-layer
surface is the policy decision API; callers must not reach into future swap,
GPU, or NIC internals to infer movement safety.
