<!-- codex-research -->
# RISC-V64 FPGA + SimpleOS Bring-Up Audit

Date: 2026-05-07

## Objective

Audit the current state for:

1. FPGA load/run and RAM update by JTAG using examples and Simple code.
2. FPGA UART specification research and UART sample run.
3. RISC-V64 Linux boot after RAM loading by JTAG.
4. RISC-V64 SimpleOS load.
5. SimpleOS boot from an SD file image and validation of Simple RISC-V64 +
   SimpleOS on RISC-V64.

## Current Status

STATUS: BLOCKED for physical FPGA boot.

Local RISC-V64 and SimpleOS artifacts are present and verified under QEMU, but
the attached Kria/K26-class FPGA target does not currently expose a usable RAM
load/readback path over JTAG, no UART bytes were observed, and this repo does not
contain a K26-compatible RISC-V64 bitstream/XSA/BOOT.BIN that can boot Linux or
SimpleOS on the physical board.

## Prompt-to-Artifact Checklist

| Requirement | Evidence | Result |
| --- | --- | --- |
| Research FPGA load/run by JTAG | `examples/09_embedded/fpga_riscv/program_and_read_addition_bscan.tcl` documents the existing 7-series BSCAN addition readback path. `scripts/kria_jtag_axi_inventory.shs` regenerates the Kria hardware inventory. `build/kria_jtag_axi/jtag_axi_inventory.txt` sees target `xck26_0` and `arm_dap_1`. | Partial. JTAG target is visible, but this is not a RAM loader. |
| Check RAM update by JTAG | `scripts/kria_jtag_axi_inventory.shs` checks Vivado hardware manager for JTAG-to-AXI objects. Current `build/kria_jtag_axi/jtag_axi_inventory.txt` reports `hw_axis_count=0`. | Blocked. No JTAG-to-AXI RAM access object is exposed. |
| Use Simple code where practical | `scripts/os/simpleos_fat32_image_list.spl` inspects the SD/FAT32 image in Simple. `doc/07_guide/hardware/fpga/xilinx_fpga_board_bringup.md` defines the SimpleOS purity boundary. | Done for repo-side inspection. Physical JTAG/UART/Vivado control remains host lab tooling. |
| Research UART spec | AMD Kria FTDI documentation says AMD carrier cards use FTDI for USB-JTAG/UART, and AMD KV260/Kria docs describe USB-UART as the command-line path. Local device evidence shows `/dev/ttyUSB1`, `/dev/ttyUSB2`, and `/dev/ttyUSB3` from `Xilinx_ML_Carrier_Card`. | Researched enough for the current board family. Exact live UART mapping still needs target firmware or bitstream output. |
| Run UART sample | `scripts/kria_uart_check_sample.shs` regenerates UART captures. Current `build/kria_uart_check/*` contains captures for ttyUSB1/2/3. All raw/text files are 0 bytes. | Run attempted; no UART output observed. |
| Load RISC-V64 and Linux after RAM JTAG loading | No K26-compatible RISC-V64 softcore bitstream, no RAM loader, and no Linux payload path are present. Existing `mlk_s02_100t_assumed_rv64_wrapper.vhd` ties instruction/data memory reads to zero. | Blocked. |
| Load RISC-V64 and SimpleOS | `build/os/simpleos_riscv64_smf_fs.elf` is a 64-bit RISC-V ELF. `build/os/simpleos_riscv64_qemu.log` shows `SIMPLEOS_RISCV_SMF_FS_PASS` and `TEST PASSED`. | Verified in QEMU, not on physical FPGA. |
| Boot from SD file image with SimpleOS | `build/os/fat32-riscv64.img` is a FAT image with OEM-ID `SIMPLEOS`. `scripts/os/simpleos_fat32_image_list.spl` lists `/KERNEL.ELF`, `/SYS/...`, `/HELLO.SPL`, and related files. | SD image content verified locally. Physical SD boot not verified. |
| Check Simple RISC-V64 | `build/rv64_bringup_check/hello_riscv64.elf` is a 64-bit RISC-V ELF. `build/rv64_bringup_check/hello_riscv64_qemu.log` prints `Hello, RISC-V 64!`. | Verified in QEMU. |

## Fresh Verification Evidence

Commands run:

```bash
bin/simple check scripts/os/simpleos_fat32_image_list.spl
bin/simple run scripts/os/simpleos_fat32_image_list.spl -- build/os/fat32-riscv64.img
sh -n scripts/kria_jtag_axi_inventory.shs
sh -n scripts/kria_uart_check_sample.shs
SECONDS_TO_READ=1 sh scripts/kria_uart_check_sample.shs
file build/rv64_bringup_check/hello_riscv64.elf build/os/simpleos_riscv64_smf_fs.elf build/os/fat32-riscv64.img
```

Key observed markers:

- `Checking scripts/os/simpleos_fat32_image_list.spl... OK`
- `scripts/kria_jtag_axi_inventory.shs` parses with `sh -n`
- `scripts/kria_uart_check_sample.shs` parses with `sh -n`
- `UART_STATUS=no_output`
- `/KERNEL.ELF file`
- `/SYS/APPS dir`
- `/HELLO.SPL file`
- `build/rv64_bringup_check/hello_riscv64.elf: ELF 64-bit LSB executable, UCB RISC-V`
- `build/os/simpleos_riscv64_smf_fs.elf: ELF 64-bit LSB executable, UCB RISC-V`
- `build/os/fat32-riscv64.img: DOS/MBR boot sector ... OEM-ID "SIMPLEOS"`

Existing local logs:

- `build/rv64_bringup_check/hello_riscv64_qemu.log` prints `Hello, RISC-V 64!`.
- `build/os/simpleos_riscv64_qemu.log` prints `SIMPLEOS_RISCV_SMF_FS_PASS` and `TEST PASSED`.
- `build/kria_jtag_axi/jtag_axi_inventory.txt` prints `hw_axis_count=0`.
- `build/kria_uart_check/_dev_ttyUSB*.raw` are all 0 bytes.

## Blockers

Physical FPGA boot cannot continue until at least one of these exists:

1. A K26-compatible RISC-V64 bitstream/XSA with real instruction/data RAM and a
   loader/debug path: JTAG-to-AXI, RISC-V debug module, BSCAN loader, or UART
   bootloader.
2. A Kria boot image or SD/eMMC media that starts board Linux and exposes a
   login/SSH path for software loading.
3. Authoritative K26 Vivado board/part support in the local Vivado install. The
   current install detects the physical `xck26_0` over hardware manager, but the
   repo does not contain a buildable K26 soft RISC-V design.

## Next Required Artifact

The shortest path for this objective is a K26 physical smoke bitstream with:

- one clock/reset path for the attached carrier,
- BRAM or AXI RAM connected to the soft RISC-V64 core,
- a JTAG-loadable memory path or UART bootloader,
- a UART boot marker,
- a minimal Simple/RISC-V64 payload that writes a known RAM word and prints a
  marker.

Only after that exists can the RAM-update-by-JTAG, physical UART, physical
SimpleOS load, and Linux/SimpleOS boot claims be verified.

## References

- AMD Kria SOM CC FTDI Design Guide:
  https://xilinx.github.io/kria-apps-docs/creating_applications/2022.1/build/html/docs/FTDI_EEPROM_design_guide.html
- AMD KV260 Boot Devices and Firmware Overview:
  https://docs.amd.com/r/en-US/ug1089-kv260-starter-kit/Boot-Devices-and-Firmware-Overview
