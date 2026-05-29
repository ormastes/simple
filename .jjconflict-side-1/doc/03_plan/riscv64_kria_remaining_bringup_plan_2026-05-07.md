# RISC-V64 Kria Remaining Bring-Up Plan - 2026-05-07

## Goal

Finish the physical RISC-V64/Kria bring-up after local Simple and QEMU/GHDL
proofs are already available.

## Current Proven Local Artifacts

- `build/rv64_bringup_check/hello_riscv64_qemu.log` contains
  `Hello, RISC-V 64!`.
- `build/test-artifacts/feature/baremetal/ghdl_generated_riscv64_linux_handoff/result.json`
  reports `"status": "passed"`.
- `build/os/simpleos_riscv64_qemu.log` contains
  `SIMPLEOS_RISCV_SMF_FS_PASS` and `TEST PASSED`.
- `build/os/fat32-riscv64.img` is a FAT image with OEM-ID `SIMPLEOS`.

## Remaining Blockers

1. Vivado K26 device support is missing or incomplete:
   `build/kria_vivado_add/k26_part_check.log` reports `K26_PART_COUNT=0` and
   `KRIA_BOARD_PART_COUNT=0`.
2. No K26/Kria/KV260/KR260 `.bit`, `.xsa`, `.pdi`, `BOOT.BIN`, or `.wic`
   artifact is present in the workspace.
3. The detected JTAG target has no RAM update path:
   `build/kria_jtag_axi/jtag_axi_inventory.txt` reports `hw_axis_count=0`.
4. UART capture has not produced board output:
   `build/kria_uart_check/` captures for `/dev/ttyUSB1`, `/dev/ttyUSB2`, and
   `/dev/ttyUSB3` are 0 bytes.
5. No removable SD block device is currently visible from `lsblk`.

## Remaining Work

1. Install or repair Kria/K26 Vivado device support, then rerun the K26 part
   check and require nonzero K26/Kria availability.
2. Build or provide a K26-compatible RISC-V64 hardware artifact with:
   - soft RISC-V64 core,
   - RAM connected to the core,
   - one RAM/program loader path: JTAG-to-AXI, RISC-V debug module, BSCAN
     loader, or UART bootloader,
   - UART mapped to the actual carrier-board USB-UART pins.
3. Program the K26/Kria bitstream and verify the loader path can write RAM.
4. Run the UART example and capture nonempty output from the correct
   `/dev/ttyUSB*` port.
5. Load the generated RV64 Linux handoff payload through the verified RAM path
   and capture physical boot/handoff evidence.
6. Load SimpleOS through the verified path and capture physical boot evidence.
7. Write `build/os/fat32-riscv64.img` or a Kria-compatible SimpleOS image to
   removable media and capture SD boot evidence.

## Completion Criteria

The physical bring-up is complete only when the report contains:

- K26/Kria Vivado catalog check with nonzero device/board availability, or a
  provided compatible bitstream/XSA/PDI.
- JTAG/RISC-V-debug/BSCAN/UART loader proof that RAM can be updated.
- Nonempty UART transcript from the board.
- Physical RISC-V64 Linux handoff boot evidence.
- Physical RISC-V64 SimpleOS boot evidence.
- Physical SD boot evidence for the SimpleOS image.

