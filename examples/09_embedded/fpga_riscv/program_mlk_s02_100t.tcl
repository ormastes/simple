# MLK-S02-100T programming scaffold
#
# Status:
# - template only
# - not a verified hardware programming flow yet

set bitstream "build_mlk_s02_100t/simple_mlk_s02_100t.runs/impl_1/mlk_s02_100t_wrapper_stub.bit"

if {![file exists $bitstream]} {
    puts "ERROR: Bitstream not found at $bitstream"
    puts "Run build_mlk_s02_100t.tcl after completing the XDC and top-level integration."
    exit 1
}

open_hw_manager
connect_hw_server
open_hw_target

set device [lindex [get_hw_devices] 0]
current_hw_device $device
set_property PROGRAM.FILE $bitstream $device

puts "Programming scaffold reached device selection."
puts "Do not treat this as a verified MLK-S02-100T programming flow until a real bitstream has been built and tested."

close_hw_target
disconnect_hw_server
close_hw_manager
