# Feature Expert: SimpleOS CXL and Device Processes

## What this is

The canonical routing note for SimpleOS user-space drivers, device placement,
capability-backed queues, DMA/IOMMU isolation, CXL memory, and the phrase
"driver in device."

## Non-negotiable meanings

- `HostIsolated` is the default for hardware-owning drivers.
- `HostColocated` is a measured optimization with a shared failure boundary.
- `CoprocessorRemote` uses a proxy node and bounded transport to another CPU.
- `DeviceResident` requires a programmable endpoint, secure loading, watchdog,
  reset, interrupts/DMA access, and an explicit host-device transport.
- CXL Type 3 is memory. It does not execute a driver.
- Type 3 host IPC is `CxlHostMapped`, not `CxlDeviceCoherent`.
- UNO Q is `NoCxl` unless new board-level evidence proves otherwise.

## Source of truth

| Artifact | Role |
|---|---|
| `doc/07_guide/platform/simpleos/cxl_device_process_architecture.md` | Entry guide and evidence gates |
| `doc/01_research/local/simpleos_cxl_device_process_architecture.md` | Repository assessment |
| `doc/01_research/domain/simpleos_cxl_device_process_architecture.md` | External constraints and prior art |
| `doc/02_requirements/feature/simpleos_cxl_device_process_architecture.md` | Selected Feature Bundle A |
| `doc/02_requirements/nfr/simpleos_cxl_device_process_architecture.md` | Selected NFR-B targets |
| `doc/03_plan/agent_tasks/simpleos_cxl_device_process_architecture.md` | Exclusive ownership and parallel waves |

## Agent workflow

1. Preserve the kernel-protection/user-policy split.
2. Freeze versioned contracts before parallel implementation starts.
3. Implement the real process/capability/DMA boundary before CXL policy.
4. Use isolated xHCI -> HID -> compositor as the first device-process proof.
5. Implement QEMU-testable CXL Type 3 L0-L3 before accelerator semantics.
6. Keep control recovery outside CXL-backed memory.
7. Require generations on leases, queues, reset, restart, and hot-remove.
8. Keep physical-only rows blocked until suitable hardware exists.

## Evidence and status rule

Research documents are not implementation evidence. No executable CXL/device-
process SSpec exists yet. A CI job skipped after bootstrap failure is blocked,
not passed. Report separately:

- documentation/requirements validation;
- executable feature tests;
- QEMU functional evidence;
- real-IOMMU and physical CXL evidence.

Never upgrade one category using evidence from another.

## Parallel ownership rule

Use contract-first waves and exclusive file ownership. At most three sidecars
work alongside one merge owner. Shared ABI changes require compatibility
analysis, a version update, affected-owner review, and integration-owner merge.
The xHCI vertical slice precedes CXL region policy; CXL accelerator and physical
UNO Q lanes remain blocked until their prerequisites are available.

## Update rule

Refresh this skill whenever placement semantics, queue memory modes, capability
contracts, CXL support levels, evidence gates, or the implementation status in
the canonical guide changes.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
