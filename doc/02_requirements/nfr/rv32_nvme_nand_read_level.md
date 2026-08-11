# RV32 NVMe NAND Read-Level NFRs

- **NFR-RV32-NAND-001:** No heap, dynamic arrays, floating point, or runtime
  formatting in the RV32 boot path.
- **NFR-RV32-NAND-002:** RAM addresses and retry/refresh bounds are fixed,
  range-checked, and fit both the 64 KiB FPGA BRAM link and QEMU link layouts.
- **NFR-RV32-NAND-003:** GHDL uses both the full AXI4 adapter with a
  wait-state-injected RAM slave and the exact synthesizable BRAM SoC. The AXI
  gate must observe nonzero reads and writes inside the ELF-derived `.nandram`
  range.
- **NFR-RV32-NAND-004:** Hardware evidence records firmware ELF/bitstream hashes,
  JTAG transcript, stage markers, and final verdict; simulation is not accepted
  as physical-board evidence.
