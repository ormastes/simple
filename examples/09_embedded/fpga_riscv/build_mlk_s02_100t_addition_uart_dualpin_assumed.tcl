# MLK-S02-100T addition UART demo, dual-pin assumption probe.
#
# This provisional build drives both assumed CH340 pins with the same UART TX
# waveform to test whether the unverified UART direction claim is swapped.

set project_name "simple_mlk_s02_100t_addition_uart_dualpin_assumed"
set part "xc7a100tfgg484-2"
set top "mlk_s02_100t_addition_uart_dualpin_demo_top"
set constraints_file "constraints/mlk_s02_100t_uart_dualpin_assumed_unverified.xdc"

create_project -force $project_name ./build_mlk_s02_100t_addition_uart_dualpin_assumed -part $part
set_property target_language VHDL [current_project]

add_files -norecurse {
    rtl/addition_demo.vhd
    rtl/mlk_s02_100t_addition_uart_dualpin_demo_top.vhd
}
set_property file_type {VHDL 2008} [get_files *.vhd]

add_files -fileset constrs_1 -norecurse $constraints_file
set_property top $top [current_fileset]

update_compile_order -fileset sources_1
synth_design -top $top -part $part
opt_design
place_design
route_design
write_bitstream -force "build_mlk_s02_100t_addition_uart_dualpin_assumed/${top}.bit"

puts "Wrote build_mlk_s02_100t_addition_uart_dualpin_assumed/${top}.bit"

