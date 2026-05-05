# Program the BSCAN addition demo and verify the FPGA result over JTAG.
#
# Expected readback is 0x08 because the RTL computes 3 + 5 and captures the
# 5-bit sum in an 8-bit USER1 data register.

set bitstream "build_mlk_s02_100t_addition_bscan/mlk_s02_100t_addition_bscan_demo_top.bit"
set expected "08"

open_hw
connect_hw_server

set targets [get_hw_targets]
if {[llength $targets] == 0} {
    error "No Vivado hardware targets found"
}

current_hw_target [lindex $targets 0]
open_hw_target

set devices [get_hw_devices]
if {[llength $devices] == 0} {
    error "No Vivado hardware devices found"
}

set device [lindex $devices 0]
current_hw_device $device
refresh_hw_device $device
set_property PROGRAM.FILE $bitstream $device
program_hw_devices $device
puts "PROGRAMMED $device with $bitstream"

close_hw_target
current_hw_target [lindex [get_hw_targets] 0]
open_hw_target -jtag_mode on

# 7-series USER1 instruction is 0x02 with a 6-bit instruction register.
set ir_tdo [scan_ir_hw_jtag 6 -tdi 02]
set dr_tdo [scan_dr_hw_jtag 8 -tdi 00]
puts "BSCAN_USER1_IR_TDO $ir_tdo"
puts "BSCAN_USER1_DR_TDO $dr_tdo"

if {[string equal -nocase $dr_tdo $expected] != 1} {
    error "Addition BSCAN readback mismatch: expected 0x$expected, got 0x$dr_tdo"
}

puts "ADDITION_BSCAN_PASS 3+5=8"
close_hw_target
disconnect_hw_server
close_hw
