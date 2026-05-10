# RISC-V FPGA Linux Agent Tasks

Current generated-Linux track:

1. Keep the preparation contract and executable lane validation green without restating this file as the canonical Linux platform source.
2. Preserve the completed helper-proof surface: writeback, branch immediate, store immediate, I-type immediate, upper immediate, execute control, execute datapath, branch datapath, control-flow datapath, memory access control, and jump immediate.
3. Keep both generated RV32 and RV64 Linux lanes authoritative in manifests, smoke scripts, and board wrappers.
4. Extend DTB and boot ROM packaging as generated Linux boot artifacts consumed by the authoritative board products.
5. Add Vivado materialization for concrete Xilinx board profiles, starting with MLK-S02-100T.
6. Add and maintain hardware boot-test runners for generated board products once FPGA access is available.
7. Continue fixing Simple compiler VHDL/codegen gaps discovered by the RTL generator, with explicit exact-shape tests for each new helper family.
