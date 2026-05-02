# RISC-V FPGA RTL Bundle

Board: `xilinx_generic` (`BOARD_PART_TBD`)

Generated bundle root: `--arch`

Included artifacts:
- board-scoped manifest: `riscv_fpga_rtl_manifest.sdn`
- Vivado plan scaffold: `vivado_project_plan.tcl`
- logical board I/O contract: `board_interface_contract.sdn`
- rv32 generated Simple source: `rv32/rtl/simple_rv32gc_core.spl`
- rv32 generated VHDL package: `rv32/rtl/simple_rv32i_core_pkg.vhd`
- rv32 generated VHDL core: `rv32/rtl/simple_rv32gc_core.vhd`
- rv32 generated support package: `rv32/rtl/rv32i_pkg.vhd`
- rv32 generated wrapper: `rv32/rtl/rv32i_generated_wrapper.vhd`
- rv64 generated Simple source: `rv64/rtl/simple_rv64gc_core.spl`
- rv64 generated VHDL package: `rv64/rtl/simple_rv64i_core_pkg.vhd`
- rv64 generated VHDL core: `rv64/rtl/simple_rv64gc_core.vhd`

Boundary:
- This bundle is the authoritative source for runner-consumed generated-core RTL.
- Generated-core runners must compile RTL only from the emitted bundle directories such as `rv32/rtl`, `rv64/rtl`, and the optional experimental `rv32_linux/rtl`.
- The experimental RV32 Linux lane is a non-authoritative bring-up cross-check. It does not replace the default RV32 baremetal proof lane or the default RV64 Linux proof lane.
- It does not prove constraints completeness, synthesis success, programming success, or board runtime success.
