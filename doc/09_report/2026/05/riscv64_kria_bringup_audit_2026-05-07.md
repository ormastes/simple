# RISC-V64 Kria Bring-Up Audit - 2026-05-07

## Objective

Audit progress against the requested bring-up path:

1. FPGA load/run and RAM update by JTAG using examples and Simple code.
2. UART spec/example validation on the FPGA.
3. RISC-V64 Linux boot after JTAG RAM loading.
4. RISC-V64 SimpleOS boot.
5. SimpleOS SD image boot on RISC-V64.

## Current Evidence

- RV64 local execution proof exists:
  `build/rv64_bringup_check/hello_riscv64_qemu.log` contains
  `Hello, RISC-V 64!`.
- Generated RV64 Linux handoff local proof exists:
  `build/test-artifacts/feature/baremetal/ghdl_generated_riscv64_linux_handoff/result.json`
  reports `"status": "passed"`.
- SimpleOS RV64 local proof exists:
  `build/os/simpleos_riscv64_qemu.log` contains
  `SIMPLEOS_RISCV_SMF_FS_PASS` and `TEST PASSED`.
- SimpleOS SD image artifact exists:
  `build/os/fat32-riscv64.img` is a FAT image with OEM-ID `SIMPLEOS`.
- Vivado K26 catalog remains blocked:
  `build/kria_vivado_add/k26_part_check.log` reports `K26_PART_COUNT=0` and
  `KRIA_BOARD_PART_COUNT=0`.
- No K26/Kria/KV260/KR260 `.bit`, `.xsa`, `.pdi`, `BOOT.BIN`, or `.wic`
  artifact was found in the current workspace scan.

## Completion Checklist

| Requirement | Status | Evidence |
| --- | --- | --- |
| FPGA load/run | Blocked | Physical K26-compatible bitstream/design artifact missing. |
| RAM update by JTAG | Blocked | No JTAG-to-AXI/RISC-V debug/BSCAN loader path is available in the current artifact set. |
| UART example validation | Blocked | Existing UART captures were 0 bytes; no validated board UART mapping/output exists. |
| RISC-V64 Linux after JTAG RAM load | Partial local proof only | Generated GHDL handoff test passed, but physical JTAG RAM load path is absent. |
| RISC-V64 SimpleOS | Partial local proof only | QEMU/local SimpleOS RV64 passed; physical FPGA boot is not proven. |
| SD image with SimpleOS | Partial local proof only | FAT image exists; no removable SD device or board boot proof is present. |

## Stop Condition

Physical bring-up cannot continue productively until at least one of these is
available:

- K26/Kria device support installed in Vivado so K26 designs can be built.
- A K26-compatible RISC-V64 `.bit`/`.pdi`/`.xsa` with RAM and a loader/debug
  path.
- Bootable Kria SD/eMMC media with verified UART/login access.

