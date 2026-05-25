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

## Evidence

### QEMU AN505 Cortex-M33

Result: `QEMU_SMOKE_EXIT=124` because the command was intentionally bounded by
`timeout 20s`.

Serial reached the interactive shell before timeout:

- `[BOOT] SimpleOS Lite v0.5 - Cortex-M33 (ARMv8-M)`
- `[BOOT] Platform: MPS2-AN505 (QEMU)`
- `[FAULT] MemManage, BusFault, UsageFault enabled; DIV0 trap on`
- `[MPU] Enabled, 8 regions available, 4 configured`
- `[TICK] SysTick enabled (~100 Hz)`
- `[BOOT] Entering shell...`
- `SimpleOS Lite v0.5 (hardened)`

Interpretation: QEMU was checked for the current AN505 C-shim bring-up lane and
it boots with MPU enabled. This is not yet proof of the requested final pure
Simple standalone board lane because the script builds
`src/os/kernel/arch/cortex_m33/cm33_shim.c`.

### RA4M1 Build-Only

Result: `RA4M1_BUILD_EXIT=0`.

The script built `build/os/simpleos_ra4m1.elf` and reported:

- text: `21216`
- data: `0`
- bss: `7540`
- total: `28756`

Interpretation: the current RA4M1 linker/build config is runnable through
build-only mode. Physical flashing and serial verification were not run.

### STM32U585 Build-Only

Result: `STM32U585_BUILD_EXIT=0`.

The script built `build/os/simpleos_stm32u585.elf`.

Interpretation: the current STM32U585 linker/build config is runnable through
build-only mode. Physical flashing and serial verification were not run.

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
boot bridge, not the pure Simple NVMe or virtio-net driver path. The executable
readiness contract now records that as `storage_provider=c-boot-bridge` and
`network_provider=c-boot-bridge`; hardware readiness can pass, but
`real_device_pure_simple_ready` must still fail until the enabled providers are
`simple-driver`.

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

## Remaining Gaps

- Real board flashing and serial marker verification were not run for RA4M1 or
  STM32U585.
- AN505 QEMU uses the C shim, not a pure Simple board HAL.
- QEMU AN505 command has no non-interactive pass/exit marker yet, so the probe
  needs a timeout and cannot by itself close the hardening goal.
- x86_64 q35 now proves PCI enumeration for attached NVMe and virtio-net,
  NVMe identify/read/write/restore, and virtio-net queue/TX/RX. Hardware RDMA
  remains open.
