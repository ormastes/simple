# kv260_idcode_hwjtag.tcl — read the INNER Simple-TAP IDCODE (expect 0x15350067)
# through the BSCANE2 USER4 tunnel via Vivado hw_jtag RAW mode at TCK=1 MHz.
# After a TAP reset the inner DR defaults to IDCODE, so no inner IR load is
# needed: reset -> Select-DR -> Capture-DR -> Shift-DR, then shift 32 bits.
# The tck->clk CDC delays TDO by an a-priori-unknown number of TAP steps, so we
# SWEEP the capture-phase offset (guide: "sweep the CAPTURE-phase/scan-offset
# until the inner IDCODE decodes to 0x15350067, LSB-first") and print every
# candidate; the match is the true IDCODE. Outer framing == kv260_dmi_hwjtag.tcl.
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
lappend steps {0 0}
set shift_entry [llength $steps]
lappend steps {0 0}
for {set i 0} {$i<48} {incr i} {
  if {$i==47} { lappend steps {1 0} } else { lappend steps {0 0} }
}
lappend steps {1 0}
lappend steps {0 0}
lappend steps {0 0}
set bits {}
foreach pr $steps { foreach {tms tdi} $pr { lappend bits $tms; lappend bits $tdi } }
set n [llength $bits]
set hex ""; set val 0
for {set i 0} {$i<$n} {incr i} {
  set val [expr {$val | ([lindex $bits $i] << ($i%4))}]
  if {($i%4)==3} { set hex [format %x $val]$hex; set val 0 }
}
if {($n%4)!=0} { set hex [format %x $val]$hex }
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
for {set off 0} {$off<8} {incr off} {
  set base [expr {2*($shift_entry + $off)}]
  set id 0
  for {set i 0} {$i<32} {incr i} {
    set b [lindex $tbits [expr {$base + 2*$i}]]
    if {$b eq ""} { set b 0 }
    set id [expr {$id | ($b << $i)}]
  }
  set tag ""
  if {$id == 0x15350067} { set tag "  <== MATCH inner IDCODE" }
  puts "IDCODE_OFFSET=$off VALUE=0x[format %08x $id]$tag"
}
close_hw_target
close_hw_manager
