# MLK-S02-100T addition UART demo, assumption-only hardware lane.
#
# Uses constraints/mlk_s02_100t_assumed_unverified.xdc. This is for explicit
# provisional hardware probing only, not final board support evidence.

set project_name "simple_mlk_s02_100t_addition_uart_assumed"
set part "xc7a100tfgg484-2"
set top "mlk_s02_100t_addition_uart_demo_top"
set constraints_file "constraints/mlk_s02_100t_assumed_unverified.xdc"

create_project -force $project_name ./build_mlk_s02_100t_addition_uart_assumed -part $part
set_property target_language VHDL [current_project]

add_files -norecurse {
    rtl/addition_demo.vhd
    rtl/mlk_s02_100t_addition_uart_demo_top.vhd
}
set_property file_type {VHDL 2008} [get_files *.vhd]

add_files -fileset constrs_1 -norecurse $constraints_file
set_property top $top [current_fileset]

update_compile_order -fileset sources_1
synth_design -top $top -part $part
opt_design
place_design
route_design
write_bitstream -force "build_mlk_s02_100t_addition_uart_assumed/${top}.bit"

puts "Wrote build_mlk_s02_100t_addition_uart_assumed/${top}.bit"

