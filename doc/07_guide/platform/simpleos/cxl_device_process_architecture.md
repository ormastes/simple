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

## Current implementation status

This lane currently contains reviewed research, selected requirements, NFRs,
and a contract-first parallel-agent plan. It does **not** yet contain kernel,
driver-runtime, CXL, QEMU-scenario, or executable SSpec implementation.

Do not report CXL or device-process tests as passing until executable specs and
their implementation exist. A SimpleOS workflow that fails while building the
pure-Simple CLI and consequently skips QEMU proves neither success nor failure
of the proposed CXL architecture; report it as an upstream admission blocker.

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

## Evidence gates

| Claim | Minimum evidence |
|---|---|
| Driver isolation | Distinct VM/capability spaces plus denied-access tests |
| Revocation | MMIO unmap, IRQ mask, DMA detach, reset, and stale-generation rejection |
| `iommu_isolated` | Real IOMMU attachment and out-of-window DMA rejection |
| CXL Type 3 L0-L3 | QEMU topology, region, interleave, persistence, poison, and hot-remove scenarios |
| `CxlHostMapped` queue | Host processes, Type 3 backing, poison relocation, and DRAM fallback |
| `CxlDeviceCoherent` | Programmable Type 1/2 endpoint consuming the queue |
| `DeviceResident` | Signed device runtime, watchdog/reset, and independent failure evidence |

Skipped, unavailable, synthetic-marker-only, or mock-only rows remain blocked.
QEMU proves functional topology and fault behavior, not real cache-coherency
timing, fabric management, multi-host ownership, or physical performance.

## Canonical artifacts

- Requirements: `doc/02_requirements/feature/simpleos_cxl_device_process_architecture.md`
- NFRs: `doc/02_requirements/nfr/simpleos_cxl_device_process_architecture.md`
- Local research: `doc/01_research/local/simpleos_cxl_device_process_architecture.md`
- Domain research: `doc/01_research/domain/simpleos_cxl_device_process_architecture.md`
- Parallel plan: `doc/03_plan/agent_tasks/simpleos_cxl_device_process_architecture.md`
- Agent routing: `doc/00_llm_process/feature_expert/simpleos_cxl_device_process/skill.md`

Systems without a proved IOMMU report `dma_brokered`, never `iommu_isolated`.
Unavailable hardware rows remain blocked with exact resume contracts.
