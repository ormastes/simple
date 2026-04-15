# Vivado Build Script for RV32I CPU on ZedBoard
# Usage: vivado -mode batch -source build.tcl

set project_name "rv32i_zedboard"
set part "xc7z020clg484-1"
set top "zedboard_top"

# Create project
create_project -force $project_name ./build -part $part

# Add VHDL sources
add_files -norecurse {
    rtl/rv32i_pkg.vhd
    rtl/regfile.vhd
    rtl/alu.vhd
    rtl/decoder.vhd
    rtl/rv32i_core.vhd
    rtl/zedboard_top.vhd
}
set_property file_type {VHDL 2008} [get_files *.vhd]

# Add constraints
add_files -fileset constrs_1 -norecurse constraints/zedboard.xdc

# Set top module
set_property top $top [current_fileset]

# Synthesize
launch_runs synth_1 -jobs 4
wait_on_run synth_1
if {[get_property STATUS [get_runs synth_1]] != "synth_design Complete!"} {
    puts "ERROR: Synthesis failed"
    exit 1
}
puts "Synthesis complete"

# Implementation (place & route)
launch_runs impl_1 -jobs 4
wait_on_run impl_1
if {[get_property STATUS [get_runs impl_1]] != "route_design Complete!"} {
    puts "ERROR: Implementation failed"
    exit 1
}
puts "Implementation complete"

# Generate bitstream
launch_runs impl_1 -to_step write_bitstream -jobs 4
wait_on_run impl_1
puts "Bitstream generated"

# Report utilization
open_run impl_1
report_utilization -file build/utilization.txt
report_timing_summary -file build/timing.txt
puts "Reports written to build/"

close_project
