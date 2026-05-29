# MLK-S02-100T addition demo with JTAG readback through Xilinx BSCANE2.
#
# This build intentionally avoids board GPIO/UART pins. It only depends on the
# FPGA's configured JTAG TAP, which openFPGALoader has already detected.

set project_name "simple_mlk_s02_100t_addition_bscan"
set part "xc7a100tfgg484-2"
set top "mlk_s02_100t_addition_bscan_demo_top"

create_project -force $project_name ./build_mlk_s02_100t_addition_bscan -part $part
set_property target_language VHDL [current_project]

add_files -norecurse {
    rtl/addition_demo.vhd
    rtl/mlk_s02_100t_addition_bscan_demo_top.vhd
}
set_property file_type {VHDL 2008} [get_files *.vhd]

set_property top $top [current_fileset]

update_compile_order -fileset sources_1
synth_design -top $top -part $part
opt_design
place_design
route_design
write_bitstream -force "build_mlk_s02_100t_addition_bscan/${top}.bit"

puts "Wrote build_mlk_s02_100t_addition_bscan/${top}.bit"
