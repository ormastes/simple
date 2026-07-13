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

Process mappings carry both the page-table root and address-space identity.
Swap prepare, unmap, rollback, restore, and `munmap` operate on that explicit
space rather than the kernel-global page table. The page-fault path resolves the
registered process space from the active CR3; scheduler create, fork, and exec
register their address spaces. Registration failure rolls back the new page and
halts if ownership cannot be restored safely.

Production NVMe swap reserves one 4 KiB metadata slot after the declared FAT32
volume. Boot writes an ownership signature there and starts swap data after the
marker. If the marker cannot be written, swap installation fails closed.

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
bin/simple test test/02_integration/os/memory_leveling_pressure_swap_spec.spl --mode=native
bin/simple test test/01_unit/os/services/vfs/vfs_boot_memory_swap_range_spec.spl --mode=native
bin/simple test test/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.spl --mode=native
sh scripts/check/check-simpleos-memory-leveling-qemu.shs
```

The process isolation scenario creates two real sparse page-table roots, maps
the same virtual address to distinct frames, swaps exactly one mapping, proves
the other PTE remains present, and restores the swapped mapping.

The strict QEMU lane now builds and boots with a current bootstrap compiler.
Serial evidence proves configuration separation, swap roundtrip, GPU lifecycle,
NIC/DMA lifecycle, truthful unavailable physical migration, and `TEST PASSED`.
The remaining release blocker is producing a current pure-Simple CLI: the full
CLI native build exceeded 900 seconds without an artifact, so canonical
`bin/simple` verification is still pending. The Rust-built compiler remains a
bootstrap-only verifier and is not accepted as the normal tool.

Do not claim GPUDirect, RDMA hardware paging, CXL, or live GPU/NIC migration
from model or QEMU-only evidence. Real device movement needs driver-owned
migration/coherence proof.

## Kernel-base vs clang-payload placement conflict (2f boot gap)

The in-guest clang self-host path streams a 124.6 MB `clang_static` per-PT_LOAD
into ring-3 at virtual range `[0x10000000, 0x16100000)`. That range is a fixed
placement decision baked into the clang ELF link, not a leveling choice at
runtime — so the kernel's own image must be leveled to avoid it.

- `-kernel` (QEMU direct) links the clang kernel at base `0x100000` (1 MB) via
  `arch/x86_64/linker_low1mb.ld`. Kernel `.bss` stays well below `0x10000000`,
  so the clang payload VA is clear and the syscall path runs under the user CR3.
  clang-compile-over-SSH is proven **only** on this path.
- GRUB-EFI / OVMF needs the kernel at `128 MB` (a lower base faults `#UD` at
  `RIP~0x1012` in the multiboot relocator). But a 128 MB base pushes kernel
  `.bss` to ~375 MB, which **overlaps** the clang payload VA — the user-CR3
  syscall then faults. So the clang kernel is currently `-kernel`-only ("Not for
  GRUB-EFI"; see the linker comment).

This is a placement conflict, not a QEMU limitation: any real-board loader that
imposes a high kernel base collides with the clang payload's fixed VA. Fix
options, in preference order: (a) UEFI-stub entry (`efi_main`,
`--target x86_64-unknown-uefi`) so no multiboot relocator forces the high base;
(b) higher-half kernel at `0xffffffff80000000` so `.bss` never intersects the
low payload window; (c) relocate the clang payload VA out of the kernel's range.
Until one lands, the board-proxy capstone (clang kernel booting under OVMF)
stays open. See `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md` step 2f.
