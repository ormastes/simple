# jtag_dmi_tunnel.tcl — Vivado hw_jtag driver for the Simple rv32 DMI over the
# xck26 BSCANE2 USER4 tunnel (bscane2_tap_bridge v1 TMS/TDI-pair framing) at
# TCK=1 MHz. Recovered verbatim from the proven 2026-07-24 board readout.
# Usage: vivado -mode batch -source jtag_dmi_tunnel.tcl -tclargs <idle_cycles> op:addr:data ...
#   op   = 1 read, 2 write (DMI op field)
#   addr = 7-bit DMI register address (hex, no 0x)
#   data = 32-bit data (hex, no 0x)
# Prints OUTER_DR64 (chain), FREQ, and OPi_RESULT (DMI readback, lags by one op).
# Driven by read_rv32_core_jtag.shs. Do NOT change the 1 MHz calibration.
set idle_cycles [lindex $argv 0]
set ops {}
for {set a 1} {$a < [llength $argv]} {incr a} {
  set trip [split [lindex $argv $a] ":"]
  lappend ops [list [expr {"0x[lindex $trip 0]"}] [expr {"0x[lindex $trip 1]"}] [expr {"0x[lindex $trip 2]"}]]
}
lappend ops [list 0 0 0]
open_hw_manager
connect_hw_server -url localhost:3121 -allow_non_jtag
foreach t [get_hw_targets] { catch { close_hw_target $t } }
current_hw_target [lindex [get_hw_targets] 0]
open_hw_target
catch { set_property PARAM.FREQUENCY 1000000 [current_hw_target] }
close_hw_target
open_hw_target -jtag_mode true
puts "FREQ=[get_property PARAM.FREQUENCY [current_hw_target]]"
set steps {}
for {set k 0} {$k<6} {incr k} { lappend steps {1 0} }
lappend steps {0 0} 
lappend steps {1 0} 
lappend steps {1 0} 
lappend steps {0 0} 
lappend steps {0 0} 
set irval 0x11
for {set i 0} {$i<5} {incr i} {
  set b [expr {($irval >> $i) & 1}]
  if {$i==4} { lappend steps [list 1 $b] } else { lappend steps [list 0 $b] }
}
lappend steps {1 0} 
lappend steps {0 0} 
set shift_entries {}
set nops [llength $ops]
for {set oi 0} {$oi < $nops} {incr oi} {
  set trip [lindex $ops $oi]
  set op [lindex $trip 0]; set addr [lindex $trip 1]; set data [lindex $trip 2]
  set packed [expr { ($op & 0x3) | (($data & 0xffffffff) << 2) | (($addr & 0x7f) << 34) }]
  lappend steps {1 0} ;# Sel-DR
  lappend steps {0 0} ;# Cap-DR
  lappend shift_entries [llength $steps]
  lappend steps {0 0} ;# Shift-DR entry
  for {set i 0} {$i<41} {incr i} {
    set b [expr {($packed >> $i) & 1}]
    if {$i==40} { lappend steps [list 1 $b] } else { lappend steps [list 0 $b] }
  }
  lappend steps {1 0} ;# Update-DR
  lappend steps {0 0} ;# RTI
  if {$oi < $nops-1} {
    for {set k 0} {$k<$idle_cycles} {incr k} { lappend steps {0 0} }
  }
}
lappend steps {0 0} 
lappend steps {0 0} 
set bits {}
foreach pr $steps { foreach {tms tdi} $pr { lappend bits $tms; lappend bits $tdi } }
set n [llength $bits]
set hex ""
set val 0
for {set i 0} {$i<$n} {incr i} {
  set val [expr {$val | ([lindex $bits $i] << ($i%4))}]
  if {($i%4)==3} { set hex [format %x $val]$hex; set val 0 }
}
if {($n%4)!=0} { set hex [format %x $val]$hex }
puts "OUTER_BITS=$n"
run_state_hw_jtag RESET
run_state_hw_jtag IDLE
scan_ir_hw_jtag 16 -tdi 923f
set tdo [scan_dr_hw_jtag $n -tdi $hex]
set tbits {}
set tlen [string length $tdo]
for {set i 0} {$i<$n} {incr i} {
  set nib [expr {$i/4}]
  set ch [string index $tdo [expr {$tlen-1-$nib}]]
  lappend tbits [expr {(("0x$ch") >> ($i%4)) & 1}]
}
proc decode_window {tbits shift_entry_step nbits} {
  set base [expr {2*($shift_entry_step + 2)}]
  set val 0
  for {set i 0} {$i<$nbits} {incr i} {
    set b [lindex $tbits [expr {$base + 2*$i}]]
    set val [expr {$val | ($b << $i)}]
  }
  return $val
}
for {set i 0} {$i < $nops-1} {incr i} {
  set se [lindex $shift_entries [expr {$i+1}]]
  set w [decode_window $tbits $se 41]
  set wop   [expr {$w & 0x3}]
  set wdata [expr {($w >> 2) & 0xffffffff}]
  set waddr [expr {($w >> 34) & 0x7f}]
  puts "OP${i}_RESULT OP=$wop DATA=[format %08x $wdata] ADDR=[format %02x $waddr]"
}
