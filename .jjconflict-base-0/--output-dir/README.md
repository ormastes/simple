# RISC-V FPGA RTL Bundle

Board: `xilinx_generic` (`BOARD_PART_TBD`)

Generated bundle root: `--output-dir`

Included artifacts:
- board-scoped manifest: `riscv_fpga_rtl_manifest.sdn`
- Vivado plan scaffold: `vivado_project_plan.tcl`
- logical board I/O contract: `board_interface_contract.sdn`
- rv32 generated Simple source: `rv32/rtl/simple_rv32gc_core.spl`
- rv32 generated VHDL package: `rv32/rtl/simple_rv32i_core_pkg.vhd`
- rv32 generated VHDL core: `rv32/rtl/simple_rv32gc_core.vhd`
- rv64 generated Simple source: `rv64/rtl/simple_rv64gc_core.spl`
- rv64 generated VHDL package: `rv64/rtl/simple_rv64i_core_pkg.vhd`
- rv64 generated VHDL core: `rv64/rtl/simple_rv64gc_core.vhd`

Boundary:
- This bundle proves source and RTL artifact generation.
- It does not prove constraints completeness, synthesis success, programming success, or board runtime success.
