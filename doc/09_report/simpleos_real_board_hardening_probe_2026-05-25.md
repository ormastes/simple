# SimpleOS Real Board Hardening Probe - 2026-05-25

## Scope

Probe current SimpleOS hardening and real-board bring-up state for the active
real-board/QEMU hardening goal.

## Commands Run

- `timeout 20s sh scripts/run_simpleos_cortex_m33_qemu.shs`
- `timeout 40s sh scripts/run_simpleos_ra4m1.shs --build-only`
- `timeout 40s sh scripts/run_simpleos_stm32u585.shs --build-only`
- `bin/release/x86_64-unknown-linux-gnu/simple os build --arch=x86_64`
- `timeout 20s qemu-system-x86_64 -machine q35 -cpu qemu64 -m 512M -kernel build/os/simpleos_x86_64.elf -serial stdio -monitor none -display none -no-reboot -device isa-debug-exit,iobase=0xf4,iosize=0x04 -drive file=build/os/fat32-x86_64.img,if=none,id=nvme0,format=raw -device nvme,drive=nvme0,serial=simpleos0 -netdev user,id=net0 -device virtio-net-pci,netdev=net0`
- `bin/release/x86_64-unknown-linux-gnu/simple check src/os/qemu_runner_part5.spl`
- `bin/release/x86_64-unknown-linux-gnu/simple check test/unit/os/qemu_runner_spec.spl`
- `bin/release/x86_64-unknown-linux-gnu/simple test test/unit/os/qemu_runner_spec.spl`
- `bin/release/x86_64-unknown-linux-gnu/simple check src/os/drivers/pci/pci_provider.spl test/unit/os/drivers/pci/pci_provider_spec.spl`
- `bin/release/x86_64-unknown-linux-gnu/simple test test/unit/os/drivers/pci/pci_provider_spec.spl --clean`
- `bin/release/x86_64-unknown-linux-gnu/simple check src/os/services/pcimgr/pcimgr.spl src/os/drivers/pci/pci_provider.spl test/unit/os/drivers/pci/pci_provider_spec.spl`
- `bin/release/x86_64-unknown-linux-gnu/simple os build --arch=x86_64`
- `timeout 30s qemu-system-x86_64 -machine q35 -cpu qemu64 -m 512M -kernel build/os/simpleos_x86_64.elf -serial stdio -monitor none -display none -no-reboot -device isa-debug-exit,iobase=0xf4,iosize=0x04 -drive file=build/os/fat32-x86_64.img,if=none,id=nvme0,format=raw -device nvme,drive=nvme0,serial=simpleos0 -netdev user,id=net0 -device virtio-net-pci,netdev=net0`

## Evidence

### Latest q35 QEMU Rerun After Protection-Gate Wiring

Result: build and QEMU smoke passed on 2026-05-25 after the runner-facing
protection serial gate was added.

Commands:

- `bin/release/x86_64-unknown-linux-gnu/simple os build --arch=x86_64`
- `timeout 30s qemu-system-x86_64 -machine q35 -cpu qemu64 -m 512M -kernel build/os/simpleos_x86_64.elf -serial stdio -monitor none -display none -no-reboot -device isa-debug-exit,iobase=0xf4,iosize=0x04 -drive file=build/os/fat32-x86_64.img,if=none,id=nvme0,format=raw -device nvme,drive=nvme0,serial=simpleos0 -netdev user,id=net0 -device virtio-net-pci,netdev=net0`

Process result:

- Build: PASS, elapsed `5191 ms`.
- QEMU exit code: `1`, expected success for this x86_64 `isa-debug-exit`
  lane.

Serial evidence:

- `[harden] text_write_trap=pass`
- `[stage1] PCI manager initialized`
- `[pcimgr] === Device Table (7 devices) ===`
- `0:2.0 ... class=1.8` for NVMe
- `0:3.0 ... class=2.0` for virtio-net
- `[stage1] pci_count=7`
- `[stage1] nvme_pci=present`
- `[stage1] nvme_identify_read=pass`
- `[stage1] nvme_rw_restore=pass`
- `[stage1] net_pci=present`
- `[stage1] virtio_net_tx_rx=pass`
- `TEST PASSED`

Protection classification:

- `qemu_scenario_protection_board_id(x64 q35)` maps this lane to
  `x86_64-q35`.
- The captured serial contains `[harden] text_write_trap=pass`, which satisfies
  the q35 enforce-mode probe, enable, and region/page-contract evidence used by
  `qemu_scenario_protection_serial_reason(..., "enforce", serial)`.
- Protection result: `ready` for q35 QEMU enforce evidence.

Limit still open: NVMe identify/read/write/restore and virtio-net queue/TX/RX
are still C boot-bridge transfer self-tests. This QEMU run proves current q35
runtime evidence and Simple-owned PCI enumeration, not pure Simple user-space
NVMe/net driver completion.

### QEMU AN505 Cortex-M33

Latest smoke rerun result: PASS with self-terminating guest marker after adding
the AN505 QEMU smoke path.

Command:

- `timeout 30s sh scripts/run_simpleos_cortex_m33_qemu.shs --smoke`

Process result:

- QEMU exit code: `0`.
- Guest result: `TEST PASSED`.

Serial reached:

- `[qemu-smoke] mode=boot-selftest`
- `[1] Stack canary: PASS`
- `[2] Flash CRC: PASS`
- `[3] MPU enabled: PASS`
- `[4] Faults on: PASS`
- `[5] DIV0 trap: PASS`
- `[6] SysTick: PASS`
- `[7] XN enforce: PASS`
- `[8] AP-deny: PASS`
- `Result: 8/8 ALL PASSED`
- `protection_probe=pass`
- `protection_enabled=pass`
- `region_contract=pass`
- `fault_recovered=pass`
- `[qemu-smoke] selftest=pass`
- `TEST PASSED`

Interpretation: AN505 QEMU no longer needs timeout-as-normal-result for the
smoke lane. The smoke mode runs real guest checks, emits explicit protection
markers, and exits QEMU through semihosting. This proves `mps2-an505` QEMU
`fault-test` evidence for the current C-shim bring-up profile. It still does
not prove the final pure Simple board HAL because the lane builds
`src/os/kernel/arch/cortex_m33/cm33_shim.c`.

Catalog alignment: `simpleos_board_qemu_command_for_id_with_mode("mps2-an505",
..., FaultTest)` now includes `-semihosting-config enable=on,target=native`, so
the executable board catalog represents the same self-terminating smoke command
shape as `scripts/run_simpleos_cortex_m33_qemu.shs --smoke`.

Latest rerun result: `QEMU_SMOKE_EXIT=124` because the command was intentionally
bounded by `timeout 20s`.

Command:

- `timeout 20s sh scripts/run_simpleos_cortex_m33_qemu.shs`

Serial again reached the interactive shell before timeout:

- `[BOOT] SimpleOS Lite v0.5 - Cortex-M33 (ARMv8-M)`
- `[BOOT] Platform: MPS2-AN505 (QEMU)`
- `[FAULT] MemManage, BusFault, UsageFault enabled; DIV0 trap on`
- `[MPU] Enabled, 8 regions available, 4 configured`
- `[TICK] SysTick enabled (~100 Hz)`
- `[FS] In-memory filesystem: 6 files, 392 bytes used`
- `[BOOT] Entering shell...`
- `SimpleOS Lite v0.5 (hardened)`

Interpretation: QEMU was checked for the current AN505 C-shim bring-up lane and
it boots with MPU enabled. This is not yet proof of the requested final pure
Simple standalone board lane because the script builds
`src/os/kernel/arch/cortex_m33/cm33_shim.c`.

Protection classification: the captured AN505 serial contains `[MPU] Enabled`
and `regions`, so `simpleos_protection_evidence_from_serial("mps2-an505",
Enforce, "qemu", serial)` has probe, enable, region-contract, and runtime
evidence. This is ready for `enforce` mode, but not for `fault-test` because no
recovered negative access marker is emitted. The lane still lacks a
non-interactive guest pass/exit marker, so timeout `124` remains expected for
this shell smoke.

### RA4M1 Build-Only

Latest result: `RA4M1_BUILD_EXIT=0` with explicit protection mode.

Command:

- `timeout 40s sh scripts/run_simpleos_ra4m1.shs --build-only --protection=fault-test`

The script built `build/os/simpleos_ra4m1.elf` and reported:

- text: `21216`
- data: `0`
- bss: `7540`
- total: `28756`
- board marker: `board=ra4m1-uno-r4 protection=fault-test kind=pmsav7-mpu`
- profile: `c-shim-board-bringup`
- `REAL_BOARD_NOT_RUN board=ra4m1-uno-r4 reason=build-only protection=fault-test`

Interpretation: the current RA4M1 linker/build config is runnable through
build-only mode with an explicit protection selection. Physical flashing and
serial verification were not run.

### STM32U585 Build-Only

Latest result: `STM32U585_BUILD_EXIT=0` with explicit protection mode.

Command:

- `timeout 40s sh scripts/run_simpleos_stm32u585.shs --build-only --protection=fault-test`

The script built `build/os/simpleos_stm32u585.elf`.

Additional markers:

- board marker: `board=stm32u585-uno-q protection=fault-test kind=pmsav8-mpu`
- profile: `c-shim-board-bringup`
- `REAL_BOARD_NOT_RUN board=stm32u585-uno-q reason=build-only protection=fault-test`

Interpretation: the current STM32U585 linker/build config is runnable through
build-only mode with an explicit protection selection. Physical flashing and
serial verification were not run.

### QEMU x86_64 q35 PCI/NVMe/Virtio-Net

Result: build and QEMU smoke passed.

Serial reached the explicit pass marker:

- `[BOOT64] call _start`
- `[harden] text_write_trap=pass`
- `[stage1] PCI manager initialized`
- `[stage1] pci_count=5`
- `[stage1] nvme_pci=present`
- `[nvme-c] NS1: sectors=8192, sector_size=512`
- `[nvme-c] Sector 0 read OK, first bytes: EB 58 90 53 49 4D 50 4C 45 4F 53 00 02 01 20 00`
- `[nvme-c] FAT32 signature at offset 510: 0x0xaa55`
- `[stage1] nvme_identify_read=pass`
- `[stage1] nvme_rw_restore=pass`
- `[stage1] net_pci=present`
- `[net] queue 0 PFN readback=... OK`
- `[net] queue 1 PFN readback=... OK`
- `[net-tx] complete desc=...`
- `[net-rx] frame len=64 type=0x...806`
- `[net] Learned gateway MAC 52:55:0a:00:02:02`
- `[stage1] virtio_net_tx_rx=pass`
- `[stage1] PASS: Kernel boot + PCI scan`
- `TEST PASSED`

Interpretation: the q35 lane now builds without unresolved freestanding
hardening/runtime helper symbols. QEMU can enumerate the attached NVMe and
virtio-net PCI devices. NVMe identify, sector read, and a reversible
write/read/restore self-test pass against the attached raw image. Virtio-net
queue setup, TX completion, and RX frame handling pass against QEMU user-mode
networking through gateway ARP response traffic.

Provider classification: this q35 evidence currently comes from the x86_64 C
boot bridge for NVMe and virtio-net transfer self-tests, not the pure Simple
NVMe or virtio-net driver path. PCI enumeration itself has moved to
Simple-owned config-space reads. The executable readiness contract still records
storage and network as `storage_provider=c-boot-bridge` and
`network_provider=c-boot-bridge`; hardware readiness can pass, but
`real_device_pure_simple_ready` must still fail until those enabled providers
are `simple-driver`.

Follow-up Simple-side PCI progress: `src/os/drivers/pci/pci_provider.spl` now
owns config-space snapshot parsing, absent vendor rejection, BAR decoding, and
NVMe, virtio-net, e1000, and InfiniBand/RDMA classification. This is not a new
QEMU boot result; it is the next parser/enumeration slice needed before live
q35 config I/O can move out of the C boot bridge.

Follow-up PCI grant hardening: `pcimgr_grant_device()` no longer reads
`rt_pci_get_field(idx, 7)` as BAR0. That bridge field is IRQ, so the old grant
path could fabricate a BAR from an interrupt line and assign a hardcoded
4096-byte size. Grants now use `pcimgr_get_bar()` to read BAR0 through config
space, probe its size, and reject devices without real BAR evidence.

QEMU rerun after the grant hardening still reached the q35 acceptance markers:

- `[stage1] pci_count=5`
- `[stage1] nvme_pci=present`
- `[stage1] nvme_identify_read=pass`
- `[stage1] nvme_rw_restore=pass`
- `[stage1] net_pci=present`
- `[stage1] virtio_net_tx_rx=pass`
- `TEST PASSED`

The process exit code was `1`, which is the expected success code for this
`isa-debug-exit` lane.

Follow-up live PCI enumeration hardening: `pcimgr_init()`,
`pcimgr_find_by_class_i64()`, BAR reads, IRQ reads, and device dumps no longer
depend on `rt_pci_device_count()` or `rt_pci_get_field()`. They now scan q35
config I/O from Simple code. The latest QEMU rerun reported 7 devices through
the Simple path, including:

- `0:2.0 ... class=1.8` for NVMe
- `0:3.0 ... class=2.0` for virtio-net

The same run reached `nvme_identify_read=pass`, `nvme_rw_restore=pass`, and
`virtio_net_tx_rx=pass`; those transfer self-tests still use the C bridge.

Follow-up NVMe Simple contract progress: `src/os/drivers/nvme/`
now includes `nvme_controller_contract.spl`, which decodes q35-style CAP,
VS, CC, CSTS, and namespace identify facts without calling the C bridge.
The focused unit test covers the observed q35 CAP value `0x4018200f0107ff`,
the expected enable CC bits, fatal/unsupported refusal reasons, and 512-byte
namespace LBA parsing. This is not new QEMU evidence; it is the Simple-side
contract needed before the current C NVMe init/read/write self-test can be
replaced.

Follow-up user-space driver boundary: the original SimpleOS design already
places raw device passthrough behind `driver_supervisor` grants for user-space
driver capsules. `src/os/drivers/user_space_driver_contract.spl` now records
that as an executable rule for NVMe, virtio-net, e1000, and RDMA direct access.
Common driver modules may share parsers, descriptor builders, queue layouts,
and state machines, but MMIO, DMA, IRQ, and doorbell access must use a
user-space driver placement, brokered device grants, a non-secure resource
namespace, and IOMMU or grant-broker evidence. C bridge providers are refused
for pure direct-access completion.

Follow-up readiness tightening: `real_device_pure_simple_ready(...)` now calls
the direct-access policy. A provider value of `simple-driver` is no longer
sufficient by itself. Enabled NVMe, virtio-net/e1000, and hardware RDMA paths
must also carry user-space driver placement, a raw-device or resource-grant-set
token source, non-secure resource namespace evidence, shared common-driver
logic, and IOMMU or grant-broker evidence.

Follow-up boot-storage tightening: `src/os/kernel/boot/boot_fs_mount.spl` now
records the boot mount provider in `FsMountResult`. The current freestanding
NVFS/DBFS probe through `CNvmeBlockAdapterFs` is tagged
`provider=c-boot-bridge` and `pure_simple=false`; the acceptance reason is
`boot-storage-not-pure-simple:c-boot-bridge`. This prevents a successful
C-bridge boot filesystem probe from being reported as pure Simple NVMe boot
storage.

Follow-up baremetal network fail-closed tightening:
`src/os/kernel/net/driver_shim.spl` now gates send, sendfile, link-up, link
speed, and MAC reporting behind `rt_net_tx_test()` and `rt_net_rx_ready()`.
The shim no longer reports discarded sends, always-up links, fixed 1GbE speed,
or a fixed MAC address before the boot packet provider proves both TX and RX.

Follow-up protection evidence tightening:
`simpleos_protection_evidence_ready(...)` now separates board support from
runtime proof. Protection claims require a QEMU or real-board check before they
can be ready. `detect` requires a support probe, `enforce` requires probe,
enable, and region/page contract evidence, and `fault-test` also requires a
recovered negative access test. `off` and `detect` remain diagnostic and cannot
satisfy hardening acceptance.

Follow-up serial marker classification:
`simpleos_protection_evidence_from_serial(...)` now maps captured boot output
into the protection evidence object. It recognizes current AN505 MPU output
such as `[MPU] Enabled, ... regions...`, current x86 hardening evidence such as
`[harden] text_write_trap=pass`, and the stricter future markers
`protection_probe=pass`, `protection_enabled=pass`, `region_contract=pass`, and
`fault_recovered=pass`.

Follow-up runner-facing protection gate:
`qemu_protection_serial_accepts_hardening(...)` and
`qemu_protection_serial_reason(...)` now expose the same serial evidence
contract from the QEMU runner module. This gives runner/report code a single
gate for board id, selected mode, runtime source, and captured serial text.
`qemu_scenario_protection_board_id(...)` and
`qemu_scenario_protection_serial_reason(...)` also map known QEMU scenarios to
board IDs before evaluating the same gate: q35 x86_64 scenarios use
`x86_64-q35`, RISC-V virt scenarios use `riscv64-virt`, and unsupported
scenarios produce an explicit `unsupported-qemu-board:<scenario>` reason.

## Code Hardening Change

`scenario_qemu_exit_success()` now rejects x86_64 QEMU exit code `0` for
`isa-debug-exit` scenarios. Guest success for those scenarios is exit code `1`;
plain exit `0` is no longer accepted as scenario success.

## Checks

- `simple check src/os/qemu_runner_part5.spl`: PASS
- `simple check test/unit/os/qemu_runner_spec.spl`: PASS
- `simple test test/unit/os/qemu_runner_spec.spl`: FAIL, unchanged known count
  of `59` passed and `3` failed. The runner does not print failing example
  names in the captured output.
- `simple check src/os/drivers/pci/pci_provider.spl test/unit/os/drivers/pci/pci_provider_spec.spl`: PASS
- `simple test test/unit/os/drivers/pci/pci_provider_spec.spl --clean`: PASS,
  `6` examples passed.
- `simple check src/os/services/pcimgr/pcimgr.spl src/os/drivers/pci/pci_provider.spl test/unit/os/drivers/pci/pci_provider_spec.spl`: PASS
- `simple check src/os/services/pcimgr/pcimgr.spl src/os/drivers/pci/pci.spl`: PASS
- `simple check src/os/drivers/nvme/nvme_controller_contract.spl src/os/drivers/nvme/mod.spl test/unit/os/drivers/nvme/nvme_controller_contract_spec.spl`: PASS
- `simple test test/unit/os/drivers/nvme/nvme_controller_contract_spec.spl --clean`: PASS,
  `4` examples passed.
- `simple check src/os/drivers/user_space_driver_contract.spl src/os/drivers/mod.spl test/unit/os/drivers/user_space_driver_contract_spec.spl`: PASS
- `simple test test/unit/os/drivers/user_space_driver_contract_spec.spl --clean`: PASS,
  `3` examples passed.
- `simple check src/os/drivers/real_device_readiness.spl test/unit/os/drivers/real_device_readiness_spec.spl`: PASS
- `simple test test/unit/os/drivers/real_device_readiness_spec.spl --clean`: PASS,
  `5` examples passed.
- `simple check src/os/port/simpleos_board_hardening.spl test/unit/os/simpleos_board_hardening_spec.spl`: PASS
- `simple test test/unit/os/simpleos_board_hardening_spec.spl --clean`: PASS,
  `3` examples passed.
- `sh -n scripts/run_simpleos_ra4m1.shs && sh -n scripts/run_simpleos_stm32u585.shs`: PASS
- `timeout 40s sh scripts/run_simpleos_ra4m1.shs --build-only --protection=fault-test`: PASS
- `timeout 40s sh scripts/run_simpleos_stm32u585.shs --build-only --protection=fault-test`: PASS
- `simple check src/os/qemu_runner_part5.spl test/unit/os/qemu_runner_spec.spl`: PASS
- `simple test test/unit/os/qemu_runner_spec.spl --clean`: FAIL, unchanged
  coarse result of `61` passed and `3` failed. The runner does not print failing
  example names in the captured output.
- `simple os build --arch=x86_64`: PASS
- q35 QEMU with NVMe and virtio-net: PASS, expected exit code `1`

## Remaining Gaps

- Real board flashing and serial marker verification were not run for RA4M1 or
  STM32U585.
- AN505 QEMU uses the C shim, not a pure Simple board HAL.
- QEMU AN505 command has no non-interactive pass/exit marker yet, so the probe
  needs a timeout and cannot by itself close the hardening goal.
- x86_64 q35 now proves Simple-owned PCI enumeration for attached NVMe and
  virtio-net. NVMe identify/read/write/restore and virtio-net queue/TX/RX
  still pass through the C bridge. Hardware RDMA remains open.
- QEMU was not rerun for the user-space driver boundary change because it adds
  an executable policy contract and docs only; it does not alter the boot path.
- QEMU was not rerun for the pure-readiness tightening because it changes the
  acceptance contract and tests, not the boot image or runtime path.
- QEMU was not rerun for the protection-evidence contract because it changes
  the acceptance model and tests only; boot serial integration remains a
  follow-up.
- QEMU was not rerun for serial marker classification because it consumes
  captured serial text and does not change the boot image. Existing AN505 and
  q35 serial samples are now covered by unit tests.
- QEMU was not rerun for the runner-facing protection gate because it adds a
  serial acceptance helper and tests only; it does not change QEMU arguments or
  the boot image.
- QEMU was not rerun for scenario-to-board protection mapping because it is
  classification logic over already captured serial output and leaves scenario
  command construction unchanged.
