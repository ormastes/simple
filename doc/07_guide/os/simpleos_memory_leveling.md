# SimpleOS Memory Leveling

Status: Feature D integration in progress; unsupported hardware remains gated.

The existing `MemoryLevelingProfile` API remains a compatibility policy model.
The integrated memory-leveling owner adds allocation identity, bounded pressure,
swap transactions, DMA ownership, and incremental telemetry without turning the
language configuration into an operating-system configuration.

## Two Configurations

`SimpleMemoryPlacementConfig` belongs to `std.memory_leveling`. It represents
platform-neutral placement intent and acceptable capabilities. It contains no
PMM capacity, watermark, reservation, swap-slot, or driver state.

`SimpleOsMemoryLevelingConfig` belongs to the SimpleOS kernel. It owns CPU/GPU/
NIC/DMA/swap capacities, protected reservations, high/low watermarks, pressure
batch size, cooldown, swap policy, and device-safety requirements.

The configurations are independently constructed and copied. They share only
immutable tier/domain/capability values. A request adapter copies relevant
placement values; it never aliases, embeds, serializes, or mutates one config as
the other.

## Compatibility Profiles

Profiles:

- `baremetal_static`: fixed pools, no swap, no migration, DMA pin safety.
- `simpleos_default`: CPU DRAM plus optional swap/demotion for ordinary pages.
- `heterogeneous_device`: CPU, swap, GPU, NIC/RDMA, DMA-pinned, and shadow-copy
  policy states.

## Safety Rules

Device-visible pages fail closed. Pinned, mapped, in-flight, device-owned, and
dirty non-coherent allocations cannot be reclaimed, relocated, swapped, or
released. Physical contiguity is valid only when PMM proves one range; otherwise
the DMA mapping exposes every scatter/gather segment.

Pressure work is bounded by the kernel configuration and has a hard maximum of
64 candidates per call. Stats are maintained by lifecycle events and do not scan
PMM or the allocation registry when queried.

Swap commits only after bytes and checksum are stored. Restore validates content,
commits the CPU mapping, and then releases the slot. Failure leaves the original
owner intact or marks an unrecoverable rollback explicitly failed.

## Placement Adapter

Language-to-OS adapter:

- `simple_memory_iso_cpu_cold()` maps to an ordinary cold CPU page.
- `simple_memory_device_gpu()` maps to a GPU-resident page and rejects swap.
- `simple_memory_network_registered()` maps to NIC-registered memory.
- `simple_memory_dma_pinned()` maps to DMA-pinned memory.

## Hardware Target Gate

- `simple_memory_x86_cpu_real()`, `simple_memory_arm_cpu_real()`, and
  `simple_memory_riscv_cpu_real()` apply the CPU page policy when marked with
  real evidence.
- `simple_memory_vulkan_gpu_real()`, `simple_memory_metal_gpu_real()`,
  `simple_memory_cuda_gpu_real()`, and `simple_memory_rdma_nic_real()` are
  recognized as real device-memory targets, but remain pinned/fail-closed.
- `simple_memory_vulkan_gpu_readback_real()` and
  `simple_memory_cuda_gpu_readback_real()` return `pin_device` when readback
  proof exists. `simple_memory_metal_gpu_readback_real()` is implemented but not
  tested in this lane.
- `memory_leveling_real_hardware_decide(profile, intent)` rejects model-only
  hardware claims with `real-hardware-evidence-required`.

QEMU can prove virtio descriptor ownership, protected reclaim, and swap behavior.
It does not prove physical GPU-local migration, GPUDirect, RDMA paging,
non-coherent cache maintenance, or IOMMU isolation. Those capabilities must
remain unavailable until a hardware owner and evidence command are recorded.

## Focused Evidence

```sh
bin/simple test test/03_system/os/simpleos_memory_leveling_spec.spl --mode=interpreter
```

Do not claim GPUDirect, RDMA hardware paging, CXL, or live GPU/NIC migration
from model or QEMU-only evidence. Real device movement needs driver-owned
migration/coherence proof.
