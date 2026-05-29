# MLK-S02-100T addition demo Vivado build script
#
# This script is intentionally guarded: the committed MLK-S02-100T XDC is still
# a placeholder, so Vivado must not produce a board bitstream until authoritative
# clock/button/LED pin constraints are present.

set project_name "simple_mlk_s02_100t_addition_demo"
set part "xc7a100tfgg484-2"
set top "mlk_s02_100t_addition_demo_top"
set constraints_file "constraints/mlk_s02_100t.xdc"

set fp [open $constraints_file r]
set xdc_text [read $fp]
close $fp

if {[string first "<CLK25_PIN>" $xdc_text] >= 0 ||
    [string first "<LED0_PIN>" $xdc_text] >= 0 ||
    [string first "<BTN0_PIN>" $xdc_text] >= 0} {
    puts "ERROR: $constraints_file still contains placeholder MLK-S02-100T pins."
    puts "Import the authoritative vendor XDC before building this hardware demo."
    exit 1
}

create_project -force $project_name ./build_mlk_s02_100t_addition_demo -part $part
set_property target_language VHDL [current_project]

add_files -norecurse {
    rtl/addition_demo.vhd
    rtl/mlk_s02_100t_addition_demo_top.vhd
}
set_property file_type {VHDL 2008} [get_files *.vhd]

add_files -fileset constrs_1 -norecurse $constraints_file
set_property top $top [current_fileset]

update_compile_order -fileset sources_1
synth_design -top $top -part $part
opt_design
place_design
route_design
write_bitstream -force "build_mlk_s02_100t_addition_demo/${top}.bit"

puts "Wrote build_mlk_s02_100t_addition_demo/${top}.bit"

