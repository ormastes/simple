## insert_ila_netlist.tcl
##
## Post-route netlist ILA insertion for KV260 (and similar) Vivado builds.
##
## WHY THIS EXISTS (2026-07-24, rv64 KV260 JTAG-only bring-up):
##   The project-flow ILA knob (`ENABLE_UART_ILA` / `enable_uart_ila` in
##   scripts/fpga/build_k26_rv64.shs) was DEAD CODE: the variable was set but
##   never consumed — no `create_debug_core` call existed anywhere in the
##   Vivado build TCL, so the knob did nothing. It has been deleted rather
##   than wired up, because the PROVEN recipe for this board is a netlist-level
##   ILA insertion done on the routed checkpoint, not a project-flow ILA baked
##   in at synthesis time. Two reasons a project-flow ILA does not work here:
##
##   1. Black-box caveat: the `synth_1` DCP for a design containing the Zynq
##      UltraScale+ PS out-of-context (OOC) block design FAILS DRC rule
##      INBB-3 (instantiated black box) when you try to open it standalone,
##      because the PS BD is synthesized OOC and only resolves after
##      `opt_design`/place/route pull the OOC netlist back in. A project-flow
##      ILA (`create_debug_core` before synth, or via the IP integrator debug
##      hub) fights this same black-box resolution order and is fragile.
##   2. This recipe was proven by hand against the IMPL_1 ROUTED checkpoint
##      (`*_routed.dcp`), where the black box is already resolved and all
##      nets/cells are concrete — inserting debug cores here is well-supported
##      by Vivado (see UG908) and takes ~15 minutes end to end on this design.
##
## WHAT THIS SCRIPT DOES
##   1. Opens the routed checkpoint.
##   2. Creates one `ila` debug core (`u_ila_0`) sized by CLI args.
##   3. Connects its clock to the caller-supplied clock net.
##   4. Connects probe0 to every net tagged `MARK_DEBUG` in the design (or to
##      an explicit probe-net list, if supplied) — this mirrors the proven
##      recipe used to observe `clk_core` toggling (or, in the KV260 PS-clock
##      case, NOT toggling — see doc/08_tracking/bug/
##      kv260_ps_bd_pl_clk0_unreachable_jtag_bringup_2026-07-24.md).
##   5. Runs `implement_debug_core`, re-places, re-routes, and writes out a
##      fresh bitstream + debug probes (.ltx) file next to the routed
##      checkpoint.
##
## USAGE
##   vivado -mode batch -source scripts/fpga/insert_ila_netlist.tcl \
##       -tclargs <routed.dcp> <out_prefix> <clock_net> [probe_net ...]
##
##   <routed.dcp>   Path to the impl_1 ROUTED checkpoint (post route_design).
##   <out_prefix>   Output path prefix; writes <out_prefix>.bit and
##                  <out_prefix>.ltx.
##   <clock_net>    Net (or pin) name to drive the ILA's clock — e.g.
##                  `k26_ps_bd_i/zynq_ultra_ps_e_0/pl_clk0` or, for the
##                  CFGMCLK-clocked designs that replace PS clocking on this
##                  board, the CFGMCLK-derived core clock net.
##   [probe_net...] Optional explicit list of nets/pins to probe. If omitted,
##                  defaults to every net matching
##                  `get_nets -hierarchical -filter {MARK_DEBUG}}` — i.e. tag
##                  the RTL signals you want visible with the MARK_DEBUG
##                  attribute and this script picks them up automatically.
##
## This script does not modify RTL, does not run synthesis, and does not
## touch the project-flow build (`build_k26_rv64.shs` / `build_k26_rv32.shs`).
## It is meant to be run standalone, by hand or from a check script, against
## an already-routed checkpoint saved from a prior build.

if {$argc < 3} {
    puts "ERROR: usage: vivado -mode batch -source insert_ila_netlist.tcl -tclargs <routed.dcp> <out_prefix> <clock_net> \[probe_net ...\]"
    exit 2
}

set routed_dcp   [lindex $argv 0]
set out_prefix   [lindex $argv 1]
set clock_net    [lindex $argv 2]
set explicit_probes [lrange $argv 3 end]

if {![file exists $routed_dcp]} {
    puts "ERROR: routed checkpoint not found: $routed_dcp"
    exit 2
}

# Default ILA sizing — matches the values proven on the rv64 KV260 bring-up.
# Override by editing these two lines if a design needs deeper/wider capture.
set ila_data_depth  4096
set ila_probe_width 64

puts "INFO: opening routed checkpoint: $routed_dcp"
open_checkpoint $routed_dcp

puts "INFO: creating debug core u_ila_0 (ila)"
create_debug_core u_ila_0 ila
set_property C_DATA_DEPTH   $ila_data_depth  [get_debug_cores u_ila_0]
set_property C_TRIGIN_EN    false            [get_debug_cores u_ila_0]
set_property C_TRIGOUT_EN   false             [get_debug_cores u_ila_0]
set_property C_ADV_TRIGGER  false             [get_debug_cores u_ila_0]
set_property C_INPUT_PIPE_STAGES 0            [get_debug_cores u_ila_0]
set_property ALL_PROBE_SAME_MU true           [get_debug_cores u_ila_0]

puts "INFO: connecting clock net: $clock_net"
connect_debug_port u_ila_0/clk [get_nets $clock_net]

if {[llength $explicit_probes] > 0} {
    puts "INFO: using explicit probe net list ([llength $explicit_probes] nets)"
    set probe_nets [get_nets $explicit_probes]
} else {
    puts "INFO: no explicit probe nets given — defaulting to all MARK_DEBUG nets"
    set probe_nets [get_nets -hierarchical -filter {MARK_DEBUG}]
    if {[llength $probe_nets] == 0} {
        puts "ERROR: no nets found with MARK_DEBUG attribute set, and no explicit probe nets were given."
        puts "        Tag the signals you want to observe with (* MARK_DEBUG = \"true\" *) in RTL, or pass explicit probe nets."
        exit 2
    }
}

puts "INFO: connecting [llength $probe_nets] probe net(s) to probe0"
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe0]
connect_debug_port u_ila_0/probe0 $probe_nets

puts "INFO: implementing debug core"
implement_debug_core

puts "INFO: re-placing design"
place_design

puts "INFO: re-routing design"
route_design

set bit_path "${out_prefix}.bit"
set ltx_path "${out_prefix}.ltx"

puts "INFO: writing bitstream: $bit_path"
write_bitstream -force $bit_path

puts "INFO: writing debug probes: $ltx_path"
write_debug_probes -force $ltx_path

puts "ILA_NETLIST_INSERT_STATUS=ok bit=$bit_path ltx=$ltx_path"
