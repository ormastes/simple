# SimpleOS Real Board Hardening And Driver Realism Plan

## Goal

Make SimpleOS hardening evidence real enough to run on QEMU-linked hardware
lanes and physical boards. Remove pass paths that depend on dummy/fake/fallback
success, make QEMU settings match existing board configs, make MMU/MPU checks
optional but explicit per target, and evolve PCI, NVMe, network, and RDMA from
models/prototypes into realistic drivers with measurable behavior.

This plan extends:

- `doc/03_plan/crash_recovery_replan_2026-05-25.md`
- `doc/03_plan/pure_simple_lib_standalone_hw_plan.md`
- `doc/05_design/hardware_driver_safety_and_performance_2026-04-15.md`
- `doc/01_research/local/net_iommu_isolation_gate.md`
- `doc/01_research/local/net_rdma_transport.md`
- `doc/03_plan/nvfs_dbfs_real_filesystem.md`

## Immediate Finding

As of this plan, Cortex-M33 board lanes still build through
`src/os/kernel/arch/cortex_m33/cm33_shim.c`. That is useful bring-up evidence,
but it is not proof that a fully pure Simple hardware profile runs on real
boards. Any release or verification report must label this lane as
`c-shim-board-bringup` until the startup, UART, MPU, fault, and app-exec
surface is moved to Simple/HAL code.

Current probe evidence is recorded in
`doc/09_report/simpleos_real_board_hardening_probe_2026-05-25.md`: AN505 QEMU
boots to the hardened shell with MPU enabled under a bounded timeout, and the
RA4M1/STM32U585 physical-board scripts pass build-only mode. Physical flashing
and pure Simple HAL execution remain open.

## Phase 1 - False Success And Fallback Removal

1. Reject generic QEMU process success for lanes that require guest-reported
   success.
   - x86/x86_64 `isa-debug-exit` success is exit code `1`, not plain exit `0`.
   - non-x86 QEMU success is exit code `0` plus lane marker checks where markers
     are declared.
2. Rename any raw-image, grep-only, or host-side fallback checks to diagnostic
   fallback, not acceptance fallback.
3. Ban these strings from acceptance markers unless the test is explicitly
   negative:
   - `dummy`
   - `fake`
   - `stub`
   - `fallback success`
   - `synthetic pass`
4. Keep host-side test shims only inside unit tests. Production board and QEMU
   lanes must not call a fake bundle/run script.

Exit evidence:

- Focused qemu runner tests reject x86_64 exit `0` for `isa-debug-exit` lanes.
- Search report over `src/os`, `scripts/run_simpleos_*`, and board plans shows
  no acceptance marker that allows dummy/fake/stub success.

## Phase 2 - Board Catalog And Real QEMU Mapping

Add first-class board descriptors rather than ad hoc script-only boards.

Required descriptor fields:

- board id
- SoC / CPU
- QEMU machine, if any
- QEMU CPU, if any
- physical board script
- linker script
- flash base, RAM base, RAM length
- UART peripheral and serial marker contract
- MPU/MMU kind
- hardening features supported
- build profile
- run profile

Initial descriptors:

| Board | CPU | QEMU | Physical Script | Protection |
|-------|-----|------|-----------------|------------|
| `mps2-an505` | Cortex-M33 | `qemu-system-arm -machine mps2-an505 -cpu cortex-m33` | QEMU only | PMSAv8-M MPU |
| `ra4m1-uno-r4` | Cortex-M4 | no faithful QEMU target | `scripts/run_simpleos_ra4m1.shs` | PMSAv7 MPU |
| `stm32u585-uno-q` | Cortex-M33 | partial via AN505 only for CPU-class smoke | `scripts/run_simpleos_stm32u585.shs` | PMSAv8-M MPU |
| `x86_64-q35` | x86_64 | `qemu-system-x86_64 -machine q35` | PC/UEFI | paging/IOMMU |
| `riscv64-virt` | rv64gc | `qemu-system-riscv64 -machine virt` | QEMU/FPGA follow-up | Sv39 |
| `xck26-ml-carrier` | rv64gc FPGA lane | generated-linux wrapper | board bundle | Sv39/IOMMU gate |

Exit evidence:

- `simpleos_platform_target_by_name()` can resolve QEMU and physical board
  aliases without shell-script-only knowledge.
- QEMU command tests prove AN505 uses the same memory map as
  `board_an505.h`.
- Physical scripts print their board id, target, linker script, and protection
  mode before flashing.

## Phase 3 - Optional MPU/MMU Hardening Matrix

Hardening must be optional at build/run time, but the selected mode must be
visible and tested.

Modes:

- `off`: only for bring-up diagnostics; cannot satisfy hardening acceptance.
- `detect`: probe MPU/MMU and print support, but do not enforce.
- `enforce`: configure regions/page tables and fail acceptance if unavailable.
- `fault-test`: enforce plus run one negative access test and recover.

Per-target checks:

| Target | Protection | Required Checks |
|--------|------------|-----------------|
| AN505 Cortex-M33 | PMSAv8-M MPU | MPU_TYPE nonzero, flash RO+X, RAM RW, peripheral XN, sandbox violation caught |
| RA4M1 Cortex-M4 | PMSAv7 MPU | power-of-two region alignment, overlap priority, sandbox violation caught |
| STM32U585 Cortex-M33 | PMSAv8-M MPU | flash/RAM/peripheral split, app sandbox, stack guard |
| x86_64 q35 | paging + optional IOMMU | kernel/user split, NX, syscall/user transition, DMA isolation when enabled |
| riscv64 virt | Sv39 | page-table root, kernel/user split, executable bit checks, SUM/MXR policy |
| riscv32 | Sv32 where available | page-table root and user/kernel isolation |

Exit evidence:

- `test/unit/os/qemu_runner_spec.spl` covers selected mode in command/catalog
  construction.
- Existing MMU specs under `src/lib/hardware/*/mmu*.spl` run for supported
  targets.
- QEMU serial contains `protection=off|detect|enforce|fault-test`.
- Real board serial contains the same selected protection mode and result.

## Phase 4 - PCI Driver Realism

Current PCI code scans x86 config I/O ports directly. That is not enough for
modern QEMU/real boards.

Work:

1. Split PCI access into provider ports:
   - x86 config I/O method 1
   - ECAM/MMCONFIG memory-mapped config
   - no-PCI provider for MCUs and pure MMIO SoCs
2. Parse BARs correctly:
   - I/O vs memory BAR
   - 32-bit vs 64-bit BAR
   - prefetchable flag
   - size probing with restore
3. Add bus walking:
   - multifunction devices
   - PCI-to-PCI bridges
   - class/subclass/prog-if matching
4. Integrate interrupt routing:
   - legacy IRQ
   - MSI/MSI-X plan
   - fallback refusal when unsupported
5. Add QEMU fixtures:
   - q35 root complex
   - virtio-net-pci
   - NVMe PCI device

Exit evidence:

- PCI tests use a fake config provider in unit tests and QEMU q35 for live
  enumeration.
- Driver logs include vendor/device/class/BAR/IRQ/MSI data.
- Executable acceptance contract rejects PCI-backed claims on MCU boards and
  rejects unsupported provider names before any driver can report real-device
  readiness.
- Current q35 smoke builds `build/os/simpleos_x86_64.elf` and reaches:
  - `[stage1] pci_count=5`
  - `[stage1] nvme_pci=present`
  - `[stage1] nvme_identify_read=pass`
  - `[stage1] nvme_rw_restore=pass`
  - `[stage1] net_pci=present`
  - `[stage1] virtio_net_tx_rx=pass`
  - `TEST PASSED`

Current Simple-side provider status:

- DONE: `src/os/drivers/pci/pci_provider.spl` models `no-pci`,
  `x86-config-io`/`q35-config-io`, and `pci-ecam` provider selection.
- DONE: provider tests cover deterministic config-I/O and ECAM address
  construction, no-PCI refusal for MCU boards, and BAR decoding for I/O,
  32-bit MMIO, and 64-bit prefetchable MMIO BARs.
- DONE: provider tests now parse config-space snapshots into Simple-owned
  enumerated functions, reject absent vendor sentinels, and classify NVMe,
  virtio-net, e1000, and InfiniBand/RDMA candidates without a C bridge parser.
- TODO: move live q35 enumeration from the C boot bridge onto this provider
  contract.

## Phase 5 - NVMe Driver Realism

Current NVMe code describes a real init sequence, but acceptance must prove more
than structural types.

Work:

1. BAR mapping through the PCI provider.
2. Controller CAP/VS/CC/CSTS handshake with timeouts.
3. Admin queue allocation with physically contiguous DMA.
4. Identify controller and namespace.
5. Create I/O SQ/CQ.
6. Read/write LBA through a block-device trait.
7. Flush, write-zeroes, discard, and feature-policy checks.
8. Integrate with NVFS/DBFS rootfs paths.

QEMU setting:

- x86_64 q35 lane must support `-device nvme,drive=nvme0,serial=simpleos0`
  with a raw disk image.

Exit evidence:

- QEMU can enumerate NVMe via PCI.
- NVMe identify result is parsed, not hardcoded.
- A known sector read/write survives reopen.
- DBFS/NVFS boot plan can select NVMe instead of FAT carrier when enabled.
- `src/os/drivers/real_device_readiness.spl` requires PCI enumeration, NVMe
  identify, read/write evidence, and DMA isolation before `storage=nvme` is
  accepted as real hardware.

Current status:

- DONE: q35 can enumerate an attached NVMe PCI device.
- DONE: q35 boot log proves NVMe namespace identify, sector 0 read, and a
  reversible write/read/restore self-test on the last namespace sector.
- DONE: executable readiness contract records the current provider as
  `storage_provider=c-boot-bridge`, so this evidence cannot satisfy
  pure-Simple completion.
- TODO: integrate the Simple NVMe driver path instead of the current C bridge.

## Phase 6 - Network And RDMA Realism

Network must be realistic before RDMA can count.

Network work:

1. Keep virtio-net as the first QEMU-backed NIC.
2. Add descriptor ring setup, feature negotiation, MAC read, RX/TX queue, and
   interrupt/poll mode.
3. Add minimal Ethernet/ARP/IPv4/ICMP/UDP/TCP smoke as separate layers.
4. Add `network=off|virtio-net|e1000|rdma` selection.

RDMA work:

1. Keep `src/lib/nogc_async_mut/io/rdma.spl` as a model until a real provider
   exists.
2. Add explicit provider interface:
   - memory registration
   - protection domain
   - queue pair
   - completion queue
   - DMA/IOMMU isolation status
3. Add `rdma=off|model|sffi-host|device` mode.
4. Refuse `rdma=device` unless PCI/IOMMU/DMA prerequisites pass.
5. Compare RDMA against TCP on the same fixture and report p50/p95 latency and
   requests/sec.

Exit evidence:

- QEMU virtio-net lane sends and receives at least one packet.
- RDMA model cannot be reported as hardware RDMA.
- Hardware RDMA cannot be enabled without DMA/IOMMU evidence.
- `test/unit/os/drivers/real_device_readiness_spec.spl` proves model/SFFI RDMA
  are refused as hardware RDMA and that `rdma=device` needs PCI enumeration,
  a real device, DMA isolation, and IOMMU/broker evidence.

Current status:

- DONE: q35 can enumerate an attached virtio-net PCI device.
- DONE: q35 boot log proves virtio-net RX/TX queue setup, TX completion, and
  RX frame processing through QEMU user-mode gateway ARP response traffic.
- DONE: executable readiness contract records the current provider as
  `network_provider=c-boot-bridge`, so this evidence cannot satisfy
  pure-Simple completion.
- TODO: integrate the Simple virtio-net driver path instead of the current C
  boot bridge.

Pure-Simple completion gate:

- `real_device_readiness_ready(current_q35)` may pass with `c-boot-bridge`
  evidence.
- `real_device_pure_simple_ready(current_q35)` must fail until storage,
  network, and any RDMA provider fields are `simple-driver` for enabled
  hardware modes.

## Phase 7 - QEMU And Real Board Verification

QEMU commands to prove before claiming completion:

- AN505 Cortex-M33 build + run:
  - `sh scripts/run_simpleos_cortex_m33_qemu.shs`
- x86_64 q35 PCI/NVMe/network:
  - QEMU lane with q35, NVMe, virtio-net, serial log, and marker checks.
- riscv64 virt Sv39:
  - QEMU lane with MMU marker and network/storage options where available.

Real board checks:

- RA4M1:
  - build-only first
  - flash
  - serial marker for UART, MPU mode, fault-test result
- STM32U585:
  - build-only first
  - flash
  - serial marker for UART, MPU mode, fault-test result

If QEMU was not run, reports must say: `QEMU_NOT_RUN` with reason and next
command. If real hardware was not connected, reports must say
`REAL_BOARD_NOT_RUN` with board id and required tool/probe.

## Phase 8 - Implementation Order

1. Tighten QEMU exit and marker acceptance.
2. Add board descriptor catalog and tests.
3. Add optional protection mode flags through catalog/scripts/serial markers.
4. Move AN505/RA4M1/STM32U585 C-shim behavior behind a named
   `c-shim-board-bringup` profile.
5. Add pure Simple HAL equivalents for UART, MPU setup, fault-test, and SysTick.
6. Add PCI provider split and q35 enumeration test.
7. Add NVMe identify/read/write over PCI.
8. Add virtio-net realistic queue smoke.
9. Add RDMA provider gate and benchmark scaffold.

## Done Criteria

- No dummy/fake/stub/fallback pass path can satisfy SimpleOS hardening
  acceptance.
- QEMU configuration is tied to board descriptors and current board headers.
- MPU/MMU mode is optional but explicit and tested.
- At least one QEMU board lane and one physical board lane have serial evidence.
- PCI enumeration is provider-based and supports q35.
- NVMe reads/writes real sectors through PCI and DMA.
- Network sends/receives through a realistic queue-backed NIC.
- RDMA cannot claim hardware support unless PCI/DMA/IOMMU prerequisites pass.
