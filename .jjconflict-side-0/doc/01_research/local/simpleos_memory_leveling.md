# SimpleOS Memory Leveling Local Research

Status: draft research for `$sp_dev` lane `simpleos-memory-leveling`.

## Scope

The request asks for memory leveling with swap, GPU memory, network/NIC memory,
and DMA support across the Simple language model and SimpleOS. I found no
existing `memory_leveling` or `SimpleQ OS` lane. In this repo, the closest
authoritative scope is SimpleOS plus Simple's capability/memory model.

## Existing Pieces To Reuse

- `src/os/kernel/memory/vmm.spl` is the VMM hub. It already owns page-table
  flags, address spaces, VMAs, demand paging modules, and copy-in checks.
- `test/03_system/os/baremetal/feature/log_policy_spec.spl` and sibling
  `os.baremetal.profile.*` specs show an existing SimpleOS pattern for explicit
  bare-metal profiles. Memory leveling should follow that shape instead of
  forcing one complex policy on every target.
- `src/os/userlib/device.spl` defines the syscall-facing
  `DeviceDmaDescriptor` and `SharedDmaBuffer` shape: CPU address, physical
  address, device-visible address, length, cache policy, owner task/device, and
  allocation id.
- `doc/01_research/os/driver/driver_shared_dma_contract.md` and
  `doc/01_research/lib/networking/net_shared_dma_ownership.md` both identify
  `std.io.dma.SharedDmaBuffer` as the cross-driver DMA descriptor.
- `test/03_system/os/net_shared_dma_ownership_spec.spl` and
  `test/03_system/os/net_rdma_transport_spec.spl` already cover packet DMA,
  RDMA readiness, memory registration, and IOMMU/broker requirements.
- `src/lib/gc_async_mut/gpu/memory.spl` has high-level GPU arrays backed mostly
  by torch/CUDA handles. It is not an OS page-tier model and should not become
  the SimpleOS kernel interface.
- `doc/04_architecture/language/memory_model_implementation.md` documents the
  Simple language capability model (`T`, `mut T`, `iso T`, `@T`). This is the
  right language boundary: ownership/capability annotations select whether a
  page can be pinned, lent to DMA, migrated, or swapped.

## Gaps

- No single policy object classifies memory into CPU DRAM, swap, GPU VRAM,
  NIC/RDMA registered memory, CXL/remote-like memory, and DMA-pinned pages.
- No profile contract selects simpler targets such as bare-metal/static memory,
  normal SimpleOS swap, or heterogeneous GPU/NIC memory.
- No page state contract says when a page may migrate, be shadow-copied,
  stay pinned, or fail closed.
- No Simple language-facing memory placement hint exists for GPU/NIC/DMA
  traffic beyond existing capability types and driver descriptors.
- The current GPU memory surface is library/runtime handle based, not VMM-owned
  heterogeneous page management.
- The current network/RDMA surface proves registration readiness, but not
  integration with swap or tier migration policy.

## Implementation Direction

Add the smallest owner-boundary layer under `src/os/kernel/memory/`: a
pure-Simple model for page-tier metadata, profile configuration, and migration
decisions. It should not perform real hardware migration at first. It should
support these profiles:

- `baremetal_static`: no swap, no migration, fixed pools, DMA pin checks only.
- `simpleos_default`: CPU DRAM plus optional swap; device pages fail closed.
- `heterogeneous_device`: CPU, swap, GPU, NIC/RDMA, DMA-pinned, and shadowed
  states.

The policy should decide:

- `swappable`: normal anonymous/file pages.
- `gpu_resident`: pages owned by a GPU placement lease.
- `nic_registered`: pages registered with NIC/RDMA.
- `dma_pinned`: pages currently visible to a device and not swappable.
- `shadowed`: fast-tier copy may coexist with slow-tier copy.

Hardware-specific code should consume the existing DMA descriptor and RDMA
readiness gates instead of adding raw `rt_*` shortcuts.

## Open Requirement Decision

The first implementation slice should be selected from the option docs. The
smallest useful slice is a policy-only model plus SSpec coverage; real page
fault handlers, CXL hardware, and GPUDirect-like movement should come after the
policy contract is green.
