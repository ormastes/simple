# RISC-V FPGA Linux Agent Tasks

Historical track only:

1. Keep the preparation contract and executable lane validation green without restating this file as the canonical Linux platform source.
2. Preserve the completed helper-proof surface: writeback, branch immediate, store immediate, I-type immediate, upper immediate, execute control, execute datapath, branch datapath, control-flow datapath, memory access control, and jump immediate.
3. Keep RV64 as the authoritative default orchestration lane; keep RV32 parity-only unless a future requirement graduates it.
4. Extend DTB and boot ROM packaging only when the work stays inside bounded artifact generation rather than broader Linux-capable SoC claims.
5. Add Vivado materialization for a concrete Xilinx board profile.
6. Add hardware boot-test runner once FPGA access is available.
7. Continue fixing Simple compiler VHDL/codegen gaps discovered by the RTL generator, with explicit exact-shape tests for each new helper family.
