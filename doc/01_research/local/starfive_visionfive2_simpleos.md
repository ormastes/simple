<!-- codex-research -->
# StarFive VisionFive 2 SimpleOS — local research

## Scope and current evidence

The requested lane is not implemented. No owned source, script, test, or selected requirement mentions `StarFive`, `VisionFive`, or `JH7110`; existing mentions describe the board as planned or unavailable.

The host currently exposes neither a USB UART nor a USB JTAG probe: `lsusb` contains only root hubs, the integrated camera, and Bluetooth; `/dev/serial/by-id`, `/dev/ttyUSB*`, and `/dev/ttyACM*` are absent. No OpenOCD/J-Link/serial process or tool is active. Therefore the exact board and physical boot state are not yet proven.

## Reusable implementation surfaces

- `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl` owns the RV64 build catalog. It currently offers `riscv64gc-simpleos`, QEMU `virt`, generic FPGA M-mode, and XCK26 lanes, but no JH7110 board.
- `src/os/port/simpleos_board_hardening.spl` validates QEMU and XCK26 board profiles only.
- `src/os/kernel/arch/riscv64/boot.spl` is an OpenSBI S-mode kernel entry and links at `0x80200000`; this is the closest reusable boot model.
- `src/os/kernel/arch/riscv64/console.spl` and its common console code assume the QEMU ns16550 UART at `0x10000000`. JH7110 UART0 is also a 16550A at `0x10000000`, but that address coincidence is not a board contract: StarFive still needs an explicit board/FDT provider for clock, reset, pinmux, interrupt, register width, and baud configuration.
- The serial shell already dispatches `ls` to `g_vfs_readdir("/")` and formats the result through `shell_lite.spl`. Board boot must mount a real or packaged root filesystem before entering the shell.
- `src/os/realtime/jtag/openocd_probe.spl` provides a generic OpenOCD TCL client, but there is no JH7110 target/adapter configuration.
- `scripts/os/simpleos-native-build-riscv64.shs` builds a userspace/toolchain lane, not a bootable JH7110 kernel.

## Existing documents to extend, not replace

- `doc/07_guide/platform/simpleos/simpleos_baremetal_board_support.md`
- `doc/07_guide/os/simpleos_board_bringup.md`
- `doc/07_guide/hardware/fpga/simple_riscv_jtag_debugging.md`
- `doc/04_architecture/riscv32_riscv64_fpga_simpleos_production.md`

The generic FPGA work is useful precedent but does not prove JH7110 clock, pinmux, interrupt, storage, or boot compatibility.

## Recommended seam

Add a named `riscv64-starfive-jh7110` board/profile, preserve the existing OpenSBI S-mode kernel contract, introduce a JH7110 UART provider selected by board/FDT, package a deterministic root filesystem for real `ls`, and add build/load/capture tooling that treats physical UART/JTAG identity as a fail-closed precondition.

## Concurrent-work boundary

The current worktree contains unrelated compiler, browser-layout, Windows-wrapper, test, scratch, and bootstrap-repair changes. None authorizes combining those files with this lane; StarFive work must remain separately attributable.

## Connected Tigard evidence — 2026-08-15

Tigard subsequently enumerated as FTDI FT2232H `0403:6010`, USB serial `tiBMLHE7`, with EEPROM product text `port A:Serial  port B:JTAG`:

- interface A / `/dev/ttyUSB0`: UART;
- interface B / `/dev/ttyUSB1`: JTAG;
- persistent access: user `yoon` added to `dialout`; a temporary ACL enabled the current session;
- OpenOCD 0.12.0 installed from Ubuntu packages.

A passive five-second capture from channel A at 115200 8N1 produced no bytes. This proves host access but not target UART activity or correct board wiring.

Ubuntu's packaged `interface/ftdi/tigard.cfg` expects USB product text `Tigard V1.1`; this unit requires an explicit `ftdi device_desc {port A:Serial  port B:JTAG}` override. After temporarily releasing only FTDI interface B from `ftdi_sio`, OpenOCD accessed Tigard at 1 MHz and returned `JTAG scan chain interrogation failed: all ones`. The interface was rebound afterward. This result contradicts a working target scan and points to target power/reference voltage, mode selection, wiring, or inactive JTAG—not to missing host tooling.

A second scan at 100 kHz returned the same all-ones result. Adapter clock rate is therefore not a supported explanation; do not repeat scan-speed retries until VTGT, SPI/JTAG mode, target power, common ground, and TCK/TMS/TDI/TDO continuity have been physically checked.

After the connection was corrected, the bounded scan returned the expected
JH7110 TAP ID `0x07110cfd`. A direct UART read then captured 7,190 bytes and
identified a StarFive VisionFive V2 with 8 GiB DRAM, PCB revision `0xb2`,
OpenSBI v1.2, and U-Boot 2021.10. OpenSBI reports boot HART 1, S-mode next
address `0x40200000`, and DTB argument `0x42200000`. The earlier false UART
silence was caused by the wrapper's `timeout head -c` capture path; the
repository wrapper now uses a bounded `dd` read that preserves partial output.

## Live implementation evidence — 2026-08-16

The corrected chain exposes two equal-ID TAPs: E24 first and the U74 complex
second; RAM access and loading target U74 hart 1. A reversible scratch probe at
`0x48000000` passed write/read/restore. Live MMIO proved UART0 requires 32-bit
DesignWare 8250 accesses with register shift 2 and THRE polling. The admitted
pure-Simple Stage 3 compiler produced the RV64 ELF; JTAG staged the raw file at
`0x48000000`, and U-Boot `bootelf -s` entered it at `0x40200000`. The final
transcript contains ordered entry/console/filesystem/shell markers and real VFS
`ls /` entries `/bin`, `/etc`, and `/README.txt`. SBI SRST invoked from a
JTAG-installed RAM trampoline performed a proven full cold reboot; generic
OpenOCD `reset run` did not.
