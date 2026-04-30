create_project simple_riscv_fpga build/fpga/xilinx_generic/vivado -part BOARD_PART_TBD
set_property target_language VHDL [current_project]
add_files constraints/xilinx_generic.xdc
add_files build/fpga/rv32/rtl
set_property top simple_rv32gc_core [current_fileset]
add_files build/fpga/rv64/rtl
set_property top simple_rv64gc_core [current_fileset]
synth_design
