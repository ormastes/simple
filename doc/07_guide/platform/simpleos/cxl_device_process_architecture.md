# SimpleOS CXL Device-Process Architecture

## Selected direction

SimpleOS uses **Feature Bundle A** with **NFR-B mission-critical hardening**.
Hardware-owning drivers run in isolated host processes by default. The kernel
enforces identity, VM spaces, capabilities, MMIO, IRQ, DMA/IOMMU, reset, and
revocation; user services own topology, binding, protocols, recovery policy,
and client APIs.

CXL does not make a device executable. Type 3 is memory and is implemented
first through QEMU-testable discovery, regions, interleave, persistence, RAS,
poison, and hot-remove. Type 3-backed host queues use `CxlHostMapped`.
`CxlDeviceCoherent` and `DeviceResident` require separate programmable-endpoint
and physical evidence.

## Required milestone order

1. Freeze driver/device/lease/queue contracts and threat model.
2. Authenticate process identity, endpoints, capability transfer, and
   notifications.
3. Enforce MMIO, IRQ, DMA/IOMMU, reset, and hardware-effect revocation.
4. Prove synthetic driver crash and restart at a new generation.
5. Prove isolated xHCI -> USB -> HID -> inputd -> compositor recovery.
6. Implement CXL Type 3 L0-L3.
7. Prove poison-triggered relocation of a CXL-host-mapped queue to DRAM.
8. Validate UNO Q, real CXL, Type 1/2, and device-resident execution only on
   prepared physical targets.

## Canonical artifacts

- Requirements: `doc/02_requirements/feature/simpleos_cxl_device_process_architecture.md`
- NFRs: `doc/02_requirements/nfr/simpleos_cxl_device_process_architecture.md`
- Local research: `doc/01_research/local/simpleos_cxl_device_process_architecture.md`
- Domain research: `doc/01_research/domain/simpleos_cxl_device_process_architecture.md`
- Parallel plan: `doc/03_plan/agent_tasks/simpleos_cxl_device_process_architecture.md`

## Evidence boundary

QEMU proves functional topology and fault behavior, not real cache-coherency
timing, fabric management, multi-host ownership, or physical performance.
Systems without a proved IOMMU report `dma_brokered`, never `iommu_isolated`.
Unavailable hardware rows remain blocked with exact resume contracts.
