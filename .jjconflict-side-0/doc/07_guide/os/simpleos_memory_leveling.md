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

The strict QEMU lane uses modern VirtIO-GPU PCI for framebuffer backing and
transfer/flush, legacy VirtIO-block PCI for a 512-byte write/read swap round
trip, and legacy VirtIO-net PCI for observable RX/TX completion. The probe
registers the actual identity-mapped GPU and NIC DMA regions with the SimpleOS
memory-leveling manager before device submission. Physical migration remains
unavailable.

The last successful QEMU serial log observed real VirtIO-block swap I/O,
modern VirtIO-GPU framebuffer attach/transfer/flush, legacy VirtIO-net RX/TX
completion, protected manager lifecycles, and `TEST PASSED`. That artifact
predates the current `MemoryLevelingManager.get -> Some(...)` source change,
so it is useful behavioral evidence but not current-revision provenance. The
fresh canonical checker attempt failed during kernel native-build before QEMU
started; do not claim a current QEMU PASS until that checker is rerun.

Direct native pressure evidence is closed. The pure-Simple `--mode=native` runner
now invokes `native-build --backend cranelift --runtime-bundle
core-c-bootstrap`, runs the resulting ELF directly, and keeps SMF behavior in
compile mode. The core-C runtime now supplies `rt_bytes_alloc`, hosted
`rt_invlpg`, `serial_println`, and the five required incremental string-builder
exports; its focused archive ABI test passes. The explicit-target pressure ELF
reports `2 examples, 0 failures`, including byte-exact swap restoration and
swap-slot reuse.

The first Cranelift pressure ELF linked but was rejected as evidence: native
project lowering did not know that `MemBlockDevice` implements `BlockDevice`
in another compilation unit, so the live write call reached the protected
duck-dispatch trap. Native discovery now carries a project-wide
`trait -> implementation types` map into MIR lowering without duplicating
vtable definitions. The same link also exposed a stubbed `unsafe_addr_of`;
core-C now owns that array-header address primitive and the archive test checks
its export.

Earlier bootstrap attempts crashed while creating LLVM modules and the
canonical checker faulted during frontend initialization. Those failures are
superseded by the explicit-target pressure PASS and the full-bootstrap
null-safe array-length fix described below. AC-13 remains open for the fresh
QEMU build, malformed-token source-check failures, MCP recursion guard, and
repo-hygiene violations. The Rust-built compiler remains bootstrap-only and is
not accepted as the normal tool.

The explicit host-target Cranelift path now compiles the complete 29-file
pressure/swap closure without fallback symbols. Cross-module optional struct
returns require two compiler contracts: project import discovery must retain
the nested named type, and the `Some(value)` payload binding must retain that
concrete type. Native codegen materializes `OptionSome`, so matching still uses
`rt_enum_payload`; direct pointer binding is incorrect. Both contracts have
focused Rust regressions.

The final native test boundary was the MMIO test store, not swap policy.
Nested region arrays lost element updates after native reallocation, so page
table construction retained parent entries while the deeper and leaf entries
read as zero. Test-mode 8/64-bit MMIO now uses sparse flat address/value arrays,
matching the existing 16/32-bit owner and avoiding nested native array
mutation. The follow-up explicit-target pressure contract passes both
scenarios with exact restored bytes and reusable swap capacity.

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

## Native pressure/swap verification

The Rust bootstrap driver selects its direct native-project handler only when
the host target is explicit. For the pressure/swap closure, pass
`--target x86_64-unknown-linux-gnu`; omitting it delegates to the interpreted
pure-Simple worker and can time out before code generation.

Native-project discovery must preserve primitive function return types as well
as named project types. Otherwise an imported `u64` result such as
`vmm_read_pte` becomes `ANY`, and mixed tagged/raw equality can report a stale
mapping even when the live and saved physical addresses are identical.

The test-mode MMIO store must also avoid indexed mutation of global typed
arrays in native builds. Use append-only address/value entries and a forward
scan that remembers the final matching index. Reverse scans based on assigning
`addresses.len()` to a local index have not preserved the initial page-table
lookup in the direct native pressure/swap closure.

Generic typed-word array helpers must preserve the owning array's runtime
representation. Generic `[u32]`/`[u64]` arrays store tagged integer values;
packed arrays store raw words. Growth fallback through
`rt_typed_words_u32/u64_push` must not switch a generic array from tagged to
raw storage. Typed-word indices are raw `i64` values at the runtime ABI; an
index such as `8` must not be decoded as a tagged integer. Unchecked reads use
the array header to distinguish generic from packed storage, while bare data
pointer reads decode generic tagged slots. The checked u64 data-pointer path
uses its supplied header for that representation decision. Generic signed u64
loads use arithmetic untagging, and known data-pointer stores likewise consult
the header before choosing tagged generic or raw packed storage.

Native value equality is also part of the pressure-test contract. Separately
allocated arrays compare structurally across packed-byte, packed-u64, and
generic tagged storage; ancestor-pair tracking terminates cycles without
rejecting wide acyclic arrays. Core-C BDD equality routes array operands through
that owner instead of weakening byte-content assertions to identity checks.
The explicit-target pressure ELF must report `2 examples, 0 failures`.

Typed byte access has the same representation requirement. A statically typed
`[u8]` may still use generic tagged slots when created by a module initializer;
Cranelift's trusted-array path may skip header type validation, but it must read
the byte-packed flag before choosing one-byte or eight-byte slot addressing.
Core-C fallback accessors follow the same rule.

Native optional aggregate returns must be explicit. In particular,
`MemoryLevelingManager.get` and all successful `vmm_translate` paths return
`Some(value)`. Returning a bare aggregate lets the caller compile `.unwrap()`
as `rt_enum_payload(raw_pointer)`, which yields nil even though the aggregate
itself is valid.

Native array length is null-safe in every backend. Cranelift and LLVM must
branch around the trusted array-header load when the masked pointer is zero;
the Rust and core-C `rt_array_len` fallbacks return zero as well. This matters
for native module globals, whose declared array initializer may still be raw
null before the frontend's lazy state setup runs.

The full bootstrap must rebuild the Rust seed after backend changes. Reusing a
stale seed can produce successful Stage 2/3/4 artifacts that still contain the
old unchecked load. Current Stage 2 disassembly shows a zero test before the
offset-8 load, Stage 3 and Stage 4 pass, and the deployed compiler checker no
longer crashes. Release verification is still open: lib/MCP/LSP source checks
currently expose unrelated malformed-token diagnostics, the MCP interpreter
smoke hits its recursion guard, and fresh QEMU provenance fails during kernel
native-build before QEMU starts.
