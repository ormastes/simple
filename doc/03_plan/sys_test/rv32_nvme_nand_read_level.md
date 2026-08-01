# RV32 NVMe NAND Read-Level System-Test Plan

- **ST-RV32-NAND-001 / REQ-001..005,007:** host pure-logic checks cover lifecycle,
  every retry rung and exhaustion, both shift directions, ECC boundaries,
  refresh denial, block disturb, FCR failure/remap, and queue transitions.
- **ST-RV32-NAND-002 / REQ-001..006, NFR-003:** GHDL executes the RV32 ELF
  through `rv32_axi4_mem_adapter` into wait-state-injected RAM, derives the
  `.nandram` range from the ELF, and requires nonzero reads/writes plus both
  prevention and recovery markers.
- **ST-RV32-NAND-003 / REQ-001..006:** GHDL executes the same ELF on the exact
  BRAM SoC and requires every granular marker, exact live-counter evidence, and
  the final pass marker.
- **ST-RV32-NAND-004 / NFR-003:** repeat exact-BRAM GHDL with deterministic
  garbage fill.
- **ST-RV32-NAND-005 / REQ-006, NFR-004:** build/program KV260, read the USER4
  JTAG transcript, and require every marker with retained hashes.

AXI-RAM and exact-BRAM GHDL must pass before board programming. A missing compiler, board, cable, Vivado,
or JTAG response is a blocked environment, never a simulated pass.
