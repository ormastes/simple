# Vivado Hardware Programming Script
# Usage: vivado -mode batch -source program.tcl
# Programs the ZedBoard with the RV32I CPU bitstream

set bitstream "build/rv32i_zedboard.runs/impl_1/zedboard_top.bit"

if {![file exists $bitstream]} {
    puts "ERROR: Bitstream not found at $bitstream"
    puts "Run build.tcl first: vivado -mode batch -source build.tcl"
    exit 1
}

# Connect to hardware
open_hw_manager
connect_hw_server
open_hw_target

# Find the Zynq device
set device [lindex [get_hw_devices] 0]
current_hw_device $device
set_property PROGRAM.FILE $bitstream $device

# Program
program_hw_devices $device
puts "Programming complete! RV32I CPU is now running on ZedBoard."
puts "- LEDs show counter value"
puts "- Switches add to counter each loop"
puts "- Center button = reset"

close_hw_target
disconnect_hw_server
close_hw_manager
