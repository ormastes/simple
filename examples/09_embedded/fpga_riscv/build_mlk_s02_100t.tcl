# MLK-S02-100T Vivado build scaffold
#
# Status:
# - template only
# - intended board: MiLianKe MLK-S02-100T
# - not a verified synthesis flow yet
#
# Before using:
# - replace the wrapper target if you switch from the stub to a real top
# - verify the XDC pin map
# - add the actual generated or handwritten core sources needed by the wrapper

set project_name "simple_mlk_s02_100t"
set part "xc7a100tfgg484-2"
set top "mlk_s02_100t_wrapper_stub"

create_project -force $project_name ./build_mlk_s02_100t -part $part
set_property target_language VHDL [current_project]

add_files -norecurse {
    rtl/mlk_s02_100t_wrapper_stub.vhd
}
set_property file_type {VHDL 2008} [get_files *.vhd]

add_files -fileset constrs_1 -norecurse constraints/mlk_s02_100t.xdc
set_property top $top [current_fileset]

puts "MLK-S02-100T scaffold project created."
puts "This script is not a verified build flow until the XDC and top-level integration are completed."
