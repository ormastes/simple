# jtag_obs_tunnel.tcl — Vivado hw_jtag driver for the rv32 BRAM-SoC observation
# register file behind the xck26 BSCANE2 USER4 DR (soc_top_rv32_tiny_bram).
#
# Unlike jtag_dmi_tunnel.tcl (which pair-frames TMS/TDI to drive an inner TAP),
# the tiny-BRAM design has NO inner TAP: USER4 selects a plain 64-bit DR.
# Chain on a KV260: xck26 PS TAP (IR 12) + ARM DAP (IR 4). IR pattern 0x923f
# (PS TAP USER4 + DAP BYPASS) is the same proven value the DMI tunnel uses; the
# DAP contributes one BYPASS bit to the DR chain whose position (before/after
# our DR) is discovered EMPIRICALLY via the response signature:
#   resp = A55A(16) | echo of cmd(15:0) (16) | data(32)
# Lag-by-one: the response to command N is captured during scan N+1.
#
# Usage: vivado -mode batch -source jtag_obs_tunnel.tcl -tclargs cmd1 cmd2 ...
#   cmdN = 32-bit obs command in hex (no 0x). See rv32_bram_soc.vhd:
#     00000000 magic  00000001 status  00000002 pc  <word:16>0003 uartbuf word
#     00000004 ins    00000005 sp      00000006 ra  00000007 cycles
#     00000008 a0     00000009 mem-acks              5AFE000F soft reset
# Prints: ALIGN_MODE/ALIGN_OFF, then OBSi CMD=... DATA=... ECHO=... SIG=... for
# every command (decoded from the FOLLOWING scan). TCK is forced to 1 MHz (the
# proven-calibration rate; do not raise without re-proving).
set cmds {}
foreach a $argv { lappend cmds [expr {"0x$a"}] }
if {[llength $cmds] == 0} { set cmds [list 0 1 2] }

open_hw_manager
connect_hw_server -url localhost:3121 -allow_non_jtag
foreach t [get_hw_targets] { catch { close_hw_target $t } }
current_hw_target [lindex [get_hw_targets] 0]
open_hw_target
catch { set_property PARAM.FREQUENCY 1000000 [current_hw_target] }
close_hw_target
open_hw_target -jtag_mode true
puts "FREQ=[get_property PARAM.FREQUENCY [current_hw_target]]"

set NBITS 66  ;# 64-bit DR + 1 DAP bypass + 1 slack

# One DR scan: shift a 32-bit command into the chain with the command word
# starting at bit position $shift; returns the raw TDO bit list (LSB-first).
proc obs_scan {cmd shift} {
    global NBITS
    set val [expr {$cmd << $shift}]
    set nnib [expr {($NBITS + 3) / 4}]
    set hex [format %0${nnib}llx $val]
    set tdo [scan_dr_hw_jtag $NBITS -tdi $hex]
    # decode hex string -> bit list (LSB-first)
    set bits {}
    set tlen [string length $tdo]
    for {set i 0} {$i < $NBITS} {incr i} {
        set nib [expr {$i / 4}]
        set ch [string index $tdo [expr {$tlen - 1 - $nib}]]
        lappend bits [expr {(("0x$ch") >> ($i % 4)) & 1}]
    }
    return $bits
}

proc bits64 {bits off} {
    set v 0
    for {set i 0} {$i < 64} {incr i} {
        set b [lindex $bits [expr {$off + $i}]]
        if {$b eq ""} { set b 0 }
        set v [expr {$v | ($b << $i)}]
    }
    return $v
}

run_state_hw_jtag RESET
run_state_hw_jtag IDLE
scan_ir_hw_jtag 16 -tdi 923f

# --- Alignment probe: calibrate BOTH the shift-in position of the command and
# the bit offset of the response window. The probe command MUST be non-zero
# (cmd 0 is shift-invariant and once mis-calibrated shift=1: every command
# arrived right-shifted by one — cmd 2 decoded as 1, 7 as 3). Command 1
# (status) makes the correct shift unambiguous via ECHO=0001. On the proven
# KV260 chain the answer is cmd_shift=2, resp_off=1 (1 DAP bypass bit + 1
# TDI->DR pipeline bit).
set mode ""
set aoff -1
foreach try_shift {2 1 0 3} {
    obs_scan 1 $try_shift            ;# command 1 = status read
    set bits [obs_scan 1 $try_shift] ;# response appears in this scan
    for {set o 0} {$o <= 2} {incr o} {
        set w [bits64 $bits $o]
        set sig  [expr {($w >> 48) & 0xffff}]
        set echo [expr {($w >> 32) & 0xffff}]
        if {$sig == 0xA55A && $echo == 0x0001} {
            set mode $try_shift
            set aoff $o
            break
        }
    }
    if {$aoff >= 0} { break }
}
if {$aoff < 0} {
    puts "ALIGN_FAILED (no A55A/magic window found; is the tiny-BRAM bitstream programmed?)"
    # dump the probe scan raw for diagnosis
    set bits [obs_scan 0 1]
    set w [bits64 $bits 0]
    puts [format "RAW_PROBE_64=%016llx" $w]
    exit 2
}
puts "ALIGN_MODE=cmd_shift_$mode ALIGN_OFF=$aoff"

# --- Run the user command list (lag-by-one decode). -------------------------
set pend -1
set idx 0
foreach c $cmds {
    set bits [obs_scan $c $mode]
    if {$pend >= 0} {
        set w [bits64 $bits $aoff]
        puts [format "OBS%d CMD=%08x DATA=%08x ECHO=%04x SIG=%04x" \
            [expr {$idx - 1}] $pend [expr {$w & 0xffffffff}] \
            [expr {($w >> 32) & 0xffff}] [expr {($w >> 48) & 0xffff}]]
    }
    set pend $c
    incr idx
}
# flush the last response with a magic nop scan
set bits [obs_scan 0 $mode]
set w [bits64 $bits $aoff]
puts [format "OBS%d CMD=%08x DATA=%08x ECHO=%04x SIG=%04x" \
    [expr {$idx - 1}] $pend [expr {$w & 0xffffffff}] \
    [expr {($w >> 32) & 0xffff}] [expr {($w >> 48) & 0xffff}]]
puts "OBS_DONE n=$idx"
