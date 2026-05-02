if {$argc != 5} {
    puts "usage: vivado -mode batch -source scripts/vivado_mlk_s02_100t_generated_linux.tcl -tclargs <product_id> <arch> <bundle_root> <product_dir> <xdc_path>"
    exit 1
}

set product_id [lindex $argv 0]
set arch [lindex $argv 1]
set bundle_root [lindex $argv 2]
set product_dir [lindex $argv 3]
set xdc_path [lindex $argv 4]

if {$arch eq "rv32"} {
    set top "simple_rv32gc_core"
    set rtl_dir [file join $bundle_root "rv32" "rtl"]
} elseif {$arch eq "rv64"} {
    set top "simple_rv64gc_core"
    set rtl_dir [file join $bundle_root "rv64" "rtl"]
} else {
    puts "unknown arch: $arch"
    exit 1
}

if {![file isdirectory $rtl_dir]} {
    puts "missing RTL directory: $rtl_dir"
    exit 1
}
if {![file exists $xdc_path]} {
    puts "missing XDC file: $xdc_path"
    exit 1
}

set project_dir [file join $product_dir "vivado"]
file mkdir $project_dir
create_project -force $product_id $project_dir -part xc7a100t-2ffg484i
set_property target_language VHDL [current_project]

set vhdl_files [glob -nocomplain -directory $rtl_dir *.vhd]
if {[llength $vhdl_files] == 0} {
    puts "no VHDL files found in $rtl_dir"
    exit 1
}
foreach file $vhdl_files {
    add_files -norecurse $file
}
set_property file_type {VHDL 2008} [get_files *.vhd]
add_files -fileset constrs_1 -norecurse $xdc_path
set_property top $top [current_fileset]

launch_runs synth_1 -jobs 4
wait_on_run synth_1
launch_runs impl_1 -to_step write_bitstream -jobs 4
wait_on_run impl_1

set run_dir [get_property DIRECTORY [get_runs impl_1]]
set bit_candidates [glob -nocomplain -directory $run_dir *.bit]
if {[llength $bit_candidates] == 0} {
    puts "bitstream not produced under $run_dir"
    exit 1
}

set out_dir [file join $product_dir "bitstream"]
file mkdir $out_dir
set out_bit [file join $out_dir "${product_id}.bit"]
file copy -force [lindex $bit_candidates 0] $out_bit
puts "BITSTREAM: $out_bit"
