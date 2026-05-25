# SimpleOS Baremetal Board Support Audit

Date: 2026-05-25 UTC  
Scope: local host inventory, repo source inspection, and lightweight build/boot checks.

This guide separates three states:

- **Verified here**: checked on this host during this audit.
- **Source-present**: support exists in source or docs, but was not run here.
- **Not found**: no concrete SimpleOS support was found in this audit.

## Local Hardware And Tools

### Connected USB/debug devices

| Device | USB ID | Interpreted role | Local status |
|--------|--------|------------------|--------------|
| Xilinx ML Carrier FT4232H | `0403:6011` | RISC-V FPGA JTAG/UART carrier, channel A JTAG/MPSSE | Connected |
| Lauterbach Power Debug | `0897:0002` | TRACE32 debug probe | Connected |
| Arduino UNO WiFi R4 CMSIS-DAP | `2341:1002` | RA4M1 SWD/debug + serial | Connected as `/dev/ttyACM0` |
| Espressif USB JTAG/serial | `303a:1001` | ESP32-class USB JTAG/serial | Connected as `/dev/ttyACM1` |
| CH340 serial adapters | `1a86:7523` | UART bridges | Connected |
| Qualcomm QDL device | `05c6:9008` | USB download mode, not a SimpleOS board lane | Connected, not used |

Serial symlinks show the Xilinx ML Carrier card on `/dev/ttyUSB2`, `/dev/ttyUSB4`, and `/dev/ttyUSB5`; the preflight script documents `/dev/ttyUSB2` as console UART0 at 115200 baud.

### Tool availability

| Tool | Local status |
|------|--------------|
| `qemu-system-x86_64` | Available |
| `qemu-system-arm` | Available |
| `qemu-system-aarch64` | Available |
| `qemu-system-riscv32` | Available |
| `qemu-system-riscv64` | Available |
| `openocd` | Available, version 0.12.0 |
| Vivado | Available at `/home/ormastes/Xilinx/2025.2/Vivado/bin/vivado` |
| `openFPGALoader` | Available, but its `--version` option is not accepted by the installed build |
| `riscv64-unknown-elf-gcc` | Available |
| `riscv64-linux-gnu-gcc` | Available |
| `gdb-multiarch` | Available |
| `yosys` | Missing |
| `probe-rs` | Missing |
| `arm-none-eabi-gcc` | Missing |
| `riscv32-unknown-elf-gcc` | Missing |
| `x86_64-elf-gcc`, `i686-elf-gcc` | Missing |

## Verified Support Matrix

| Target | Board or platform | Debug/download path | Result in this audit |
|--------|-------------------|---------------------|----------------------|
| x86_64 | QEMU SimpleOS disk boot path | QEMU, optional GDB stub | Source-present. QEMU and PCI host tools available; not booted in this audit. |
| x86_32 | Multiboot SimpleOS arch lane | QEMU | Source-present in `src/os/kernel/arch/x86_32`; not run here. |
| ARM Cortex-M33 | QEMU MPS2-AN505 | QEMU serial console | Verified here. `scripts/run_simpleos_cortex_m33_qemu.shs` boots to `simpleos>` shell, reports MPU enabled and in-memory FS. |
| ARM Cortex-M4 | Arduino UNO R4 WiFi / RA4M1 | CMSIS-DAP SWD through OpenOCD | Build-verified here with `scripts/run_simpleos_ra4m1.shs --build-only`. Board is connected. Flash was not executed. |
| ARM Cortex-M33 | STM32U585 / Arduino UNO Q lane | ST-Link/OpenOCD/stm32prog SWD | Build-verified here with `scripts/run_simpleos_stm32u585.shs --build-only`. No matching ST-Link/UNO Q identity was confirmed in USB inventory. |
| ARM32 | QEMU and STM32 remote lanes | OpenOCD/ST-Link/TRACE32 depending on board | Source-present in `src/os/kernel/arch/arm32` and remote board docs; not run here. |
| ARM64 | QEMU `virt`/AArch64 lane | QEMU, GDB stub | Source-present in `src/os/kernel/arch/arm64`; not run here. |
| RISC-V 32 | QEMU/GHDL/remote lanes | QEMU GDB, GHDL, hardware-specific debug | Source-present with many specs. QEMU tool exists; RV32 baremetal GCC is missing locally. |
| RISC-V 64 | K26/ML carrier FPGA lane | FT4232H JTAG/MPSSE, Vivado/openFPGALoader/OpenOCD | Locally connected and partially preflighted. FT4232H, UARTs, OpenOCD, Vivado, and RISC-V64 compilers are available; Yosys and built bitstream/ELF artifacts are missing. |

## OS Feature Matrix

| Feature | Current status |
|---------|----------------|
| MMU | Source-present for x86_32, x86_64, ARM64, RISC-V32 Sv32, and RISC-V64 Sv39 under `src/os/kernel/arch/*/paging.spl`. RISC-V64 also has `riscv_mmu_trap.spl` and Sv39 tests. |
| MPU | Verified here on Cortex-M33 QEMU: boot log reports MPU enabled, 8 regions available, 4 configured. ARM32 docs describe MPU. |
| SIMD | Source-present in library/tests (`test/feature/scilib/*simd*`, `test/integration/lib/simd_stdlib_spec.spl`). Not board-verified here. |
| PCI/PCIe | Source-present in `src/os/drivers/pci/pci.spl`, `src/os/services/pcimgr/`, and `src/os/tools/dev/lspci_tool.spl`. Host PCI inventory is available through Linux `lspci`; SimpleOS PCI boot was not run here. |
| File systems | Source-present for FAT32, VFS, devfs, procfs, pipefs, DBFS/NVFS integration points. Cortex-M33 QEMU verified an in-memory filesystem at boot. |
| Shell | Verified here for Cortex-M33 QEMU boot to `simpleos>` shell. Full SimpleOS shell source exists under `src/os/apps/shell/`; Cortex-M33 has `shell_lite.spl`. |
| Filesystem boot | Source-present in `src/os/kernel/boot/boot_fs*.spl`, VFS boot init, FS exec spawn modules, and `scripts/run_simpleos_qemu.shs` FAT32 disk image path. Not run here. |
| Bootloader/OS download | Source-present and partially locally checkable. K26 uses FT4232H/JTAG and Vivado/OpenOCD/openFPGALoader. RA4M1 uses CMSIS-DAP/OpenOCD SWD. STM32U585 uses ST-Link/OpenOCD/stm32prog. |

## Commands Used

Hardware and tool inventory:

```bash
lsusb
lspci
find /dev -maxdepth 2 \( -name 'ttyACM*' -o -name 'ttyUSB*' -o -path '/dev/serial/*' \) -print
command -v qemu-system-riscv32 qemu-system-riscv64 qemu-system-x86_64 qemu-system-arm qemu-system-aarch64 openocd probe-rs riscv64-unknown-elf-gcc riscv32-unknown-elf-gcc riscv64-linux-gnu-gcc arm-none-eabi-gcc x86_64-elf-gcc i686-elf-gcc gdb-multiarch
```

SimpleOS checks:

```bash
sh scripts/check-riscv64-fpga-simpleos-preflight.shs --local-only
timeout 120s sh scripts/run_simpleos_ra4m1.shs --build-only
timeout 120s sh scripts/run_simpleos_stm32u585.shs --build-only
timeout 20s sh scripts/run_simpleos_cortex_m33_qemu.shs
```

SPipe checks attempted:

```bash
SIMPLE_LIB=src timeout 120s bin/simple test test/riscv64_fpga/preflight_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src timeout 120s bin/simple test test/riscv64_fpga/hardware_inventory_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src timeout 120s bin/simple test test/riscv64_fpga/jtag_unbind_spec.spl --mode=interpreter --clean
```

The three RISC-V FPGA SPipe checks failed in the current working tree even though the direct preflight script found the FT4232H and JTAG interface free. Treat the script output as the current hardware observation, and the SPipe results as regression evidence to investigate before claiming test-suite PASS.

## Board Bring-Up Guide

### RISC-V64 FPGA / K26 ML carrier

1. Confirm `lsusb` includes `0403:6011`.
2. Run `sh scripts/check-riscv64-fpga-simpleos-preflight.shs --local-only`.
3. If channel A is bound to `ftdi_sio`, run `sh scripts/jtag-ftdi-unbind.shs`.
4. Build or provide the FPGA bitstream and SimpleOS ELF under `build/riscv64-fpga/`.
5. Program the FPGA with Vivado or openFPGALoader.
6. Load the SimpleOS ELF over JTAG/OpenOCD or XSDB.
7. Monitor UART at 115200 baud, usually `/dev/ttyUSB2` on the connected ML carrier.

Current local blockers: `yosys` is missing and no `build/riscv64-fpga/simpleos.{elf,bin,bit}` artifacts exist.

### Arduino UNO R4 WiFi / RA4M1

1. Confirm `lsusb` includes `2341:1002`.
2. Build with `sh scripts/run_simpleos_ra4m1.shs --build-only`.
3. Flash with `sh scripts/run_simpleos_ra4m1.shs` after confirming the board can be reset safely.
4. Open the serial console at `/dev/ttyACM0` and 115200 baud.

This audit built `build/os/simpleos_ra4m1.elf` but did not flash it.

### STM32U585 / Arduino UNO Q lane

1. Build with `sh scripts/run_simpleos_stm32u585.shs --build-only`.
2. Select `FLASHER=st-flash`, `FLASHER=openocd`, or `FLASHER=stm32prog`.
3. Flash only after confirming an STM32U585-compatible probe and target are attached.

This audit built `build/os/simpleos_stm32u585.elf`; no matching ST-Link or STM32U585 USB identity was confirmed.

### Cortex-M33 QEMU / MPS2-AN505

Run:

```bash
sh scripts/run_simpleos_cortex_m33_qemu.shs
```

Expected boot evidence includes `SimpleOS Lite v0.5`, MPU enabled, in-memory filesystem initialized, and a `simpleos>` shell prompt.

## Baremetal SimpleOS Checklist

Use this checklist before marking a board as supported:

1. Board appears in `lsusb` or equivalent bus inventory.
2. Debug probe is identified and has a documented download path.
3. Build command produces an ELF or image without host-specific manual edits.
4. Flash/download command is documented and repeatable.
5. Serial or semihosting output reaches a shell, panic log, or test harness.
6. MMU/MPU expectations are explicit for the architecture.
7. Storage expectation is explicit: in-memory FS, FAT32 image, NVFS/DBFS, or none.
8. At least one SPipe or script check passes on the current host.

Do not mark a board as verified from source files alone. Use **source-present** until the build/download/boot path has been run and recorded.
