# Debugging Simple RISC-V on FPGA — JTAG over the Muxed Serial Link (and BSCANE2)

**Audience:** anyone debugging a hung/misbehaving Simple RISC-V hart — in the
`.spl` behavioral model or on the real board (KV260).
**Last verified:** 2026-07-24 (model path: probes + specs green; BSCANE2 path:
GHDL gates green, debug bitstream timing MET; board attach in progress).

Both paths reach the SAME RISC-V Debug Spec v0.13 stack — TAP → DTM
(IDCODE/DTMCS/DMI) → Debug Module → hart — which exists twice, kept
register-for-register identical:

| Layer | `.spl` model | Synthesizable VHDL |
|-------|--------------|--------------------|
| TAP/DTM | `src/lib/hardware/link_mux/dtm_route.spl` | `src/lib/hardware/debug/jtag_tap.vhd`, `riscv_dtm.vhd` |
| DM + hart glue | `src/lib/hardware/link_mux/dm_model.spl` | `riscv_debug_module.vhd`, `hart_core_glue.vhd`, `jtag_debug_chain.vhd` |

Shared constants (unit-spec-pinned, `jtag_units_spec.spl`): IDCODE
`0x15350067`, IR width 5, IR encodings IDCODE=0x01 / DTMCS=0x10 / DMI=0x11,
ABITS=7 (41-bit DMI DR `{addr[40:34], data[33:2], op[1:0]}`), regno
`0x1000+n` = GPR xn, `0x07B1` = dpc.

## Path 1 — the internal muxed JTAG over ONE serial port

The shared-link mux (`src/lib/hardware/link_mux/`) carries **log + terminal +
JTAG + ctrl on a single serial line**: COBS-framed, CRC-16-checked
(`frame.spl`), fair round-robin arbitration (`mux.spl` — a log burst can never
starve a JTAG reply; proven in-spec). The JTAG channel (`CH_JTAG` = 2) tunnels
the OpenOCD `remote_bitbang` byte protocol: host frames `'0'..'7'`/`'R'`
bytes onto CH_JTAG; the FPGA side demuxes them into the TAP and frames the
TDO `'0'/'1'` replies back.

```
host debugger ──rbb bytes──► LinkMux ──frames──► serial ──► LinkDemux ─► TAP→DTM→DMI→DM→hart
             ◄──'0'/'1'──── LinkDemux ◄─frames── serial ◄── LinkMux  ◄─ TDO
```

- **Transport profiles** (`mux.spl`): `transport_sim_loopback()` (tests),
  `transport_k26_pmod()` (KV260 PL PMOD-J2 UART H12/E10 — needs the 3.3 V
  PMOD serial adapter on real hardware), `transport_arty()`. The profile is
  the DI seam; the frame format never changes.
- **Debug a hart in the model** (works today, interpreter-only): follow
  `test/01_unit/lib/hardware/link_mux/jtag_debug_probe.spl` — it builds the
  full host↔link↔fpga loop against `soc_top_64` and demonstrates: read
  IDCODE, DTMCS, `haltreq` → `allhalted`, read dpc, read/WRITE a GPR, resume
  → `allresumeack`, with a CH_LOG burst interleaved mid-session. The
  operator-manual version is `jtag_debug_scenario_spec.spl` (generated manual:
  `doc/06_spec/01_unit/lib/hardware/link_mux/jtag_debug_scenario_spec.md`).
  Prefer extending these over print-debugging core state.
- **On hardware** this path needs the PMOD serial adapter (TX=H12, RX=E10,
  GND) — the KV260 carrier routes NO FT4232H channel to PL pins, so without
  the adapter the muxed link has no physical wire (same blocker as the UART
  soak; see the plan doc). Once wired, the host side is: demux CH_JTAG ↔
  OpenOCD `remote_bitbang` socket, log/term channels stay live on the same
  wire.

## Board-proven attach recipe (2026-07-24, KV260) — READ THIS

The BSCANE2 path below is **board-verified**: a Simple RV32 core ran a 981 s
soak on a real KV260 whose golden was read out bit-exact (`0x7EB5A8A9`) over
this JTAG stack, no UART. Two hard-won details:

1. **TCK must be slow.** The `bscane2_tap_bridge` tck→clk CDC is only proven at
   TCK ≤ core_clk/8 (core ≈ 25 MHz = CFGMCLK/2, so ≈ 3 MHz). Vivado
   `hw_jtag`'s ~15 MHz default reads **all-zeros**. Set **1 MHz**: open the
   target in NORMAL mode, `set_property PARAM.FREQUENCY 1000000
   [current_hw_target]`, close, reopen with `-jtag_mode 1`.
2. **Use Vivado `hw_jtag` raw mode, not OpenOCD.** OpenOCD's `use_bscan_tunnel`
   framing (`[ctrl][7-bit width][data][ctrl]`, FPGA generates inner TMS) is
   **structurally incompatible** with the v1 bridge (raw 2-bit TMS/TDI pairs,
   host drives every inner-TAP transition). No cfg/tcl fixes it. Enter raw JTAG
   with `open_hw_target -jtag_mode 1` (NB: `create_hw_jtag` does NOT exist in
   Vivado 2025.2), then `run_state_hw_jtag` / `scan_ir_hw_jtag` /
   `scan_dr_hw_jtag`. Chain = xck26 (idx 0, USER4 host) + arm_dap (idx 1,
   IR len 4, BYPASS → +1 DR bit). Drive the inner TAP through the USER4 DR as
   2-bit `{tms,tdi}` pairs; sweep the CAPTURE-phase/scan-offset until the inner
   IDCODE decodes to `0x15350067`, LSB-first. Sample the running soak with
   halt(DMCONTROL.haltreq→dmstatus allhalted)→abstract-read x18/x8→resume.

## Path 2 — BSCANE2 tunnel over the programming cable (board-ready)

Zero extra cabling: the debug TAP is reached through the SAME FT4232H used
for programming, via a Xilinx BSCANE2 (USER4) primitive and the
`bscane2_tap_bridge.vhd` de-framer. Enabled by the `G_DEBUG_JTAG` generate
guard on `soc_top_rv32.vhd` (default **false**; a debug bitstream sets it
true — no new top ports).

1. Build the debug bitstream (Vivado; hold `build/fpga/.vivado.lock`, ONE
   Vivado repo-wide) and program via
   `scripts/fpga/program_kv260_bitstream.shs`.
2. Attach — **one JTAG-chain client at a time** (hw_server ⊕ OpenOCD):
   - OpenOCD: `scripts/fpga/openocd_kv260_bscan.cfg` (FT4232H ch A, ZU+ PS
     TAP, `riscv use_bscan_tunnel 5 1` = DATA_REGISTER tunnel, inner IR=5).
   - Fallback: Vivado `hw_jtag` driving USER4 with the bridge's v1 framing
     directly (useful when validating tunnel framing interop — see
     `doc/03_plan/hardware/riscv/bscane2_tunnel_openocd_interop_boardverify.md`).
3. `scripts/fpga/check_kv260_jtag_debug.shs verify` — halt, read pc/GPRs,
   breakpoint, single-step, resume; fail-closed transcript.
4. **10-minute soak evidence without any UART**:
   `check_kv260_jtag_debug.shs soak` polls the running soak payload over
   JTAG — golden Adler-32 accumulates in **x8**, progress counter in **x18**
   (decoded from the payload ROM; `GOLDEN_EXPECTED=7EB5A8A9` for the staked
   COUNT=260M build) — enforcing ≥600 s wall, timestamped, golden compare.

## PS-clocked designs on KV260 (JTAG-only bring-up) — landmine

**Verdict: do not clock fabric logic from the Zynq UltraScale+ PS
(`pl_clk0`/`pl_resetn0`) when the bring-up flow is JTAG-only (no PS boot). Use
free-running `CFGMCLK` instead — the same pattern already proven for rv32.**
See `doc/08_tracking/bug/kv260_ps_bd_pl_clk0_unreachable_jtag_bringup_2026-07-24.md`
for full evidence.

Why: on this board, in a JTAG-only bring-up (the PS is never released from
POR — no U-Boot/PMU firmware boots the A53s), `pl_clk0` is gated OFF and
`pl_resetn0` sits LOW, because both are produced by the PS clock/reset
generators which only start once the PS boot ROM has run far enough to
configure the IOPLL and de-assert the FPD/LPD reset domains. Symptoms and the
investigation trail:

1. **Fabric silent, no clock activity.** A netlist ILA on the fabric core
   clock net (`clk_core`) showed it **never toggles** — proven, not
   inferred (see "Fabric-internal visibility" below).
2. **xsdb-side pokes did not fix it**, even though each looked plausible in
   isolation:
   - `PL0_REF_CTRL = 0x01010A00` — sets the PL0 reference clock to 100 MHz
     sourced from the IOPLL, but the IOPLL itself is BootROM-locked and
     never reaches lock in a JTAG-only flow.
   - Clearing bit 18 of `RST_LPD_IOU2` — un-resets the GPIO block, needed
     for further pokes, but does not touch the PL clock/reset path.
   - Setting bit 31 of `DIRM_5`/`OEN_5`/`DATA_5` (`0xFF0A0344`/`48`/`54`) —
     drives EMIO95 high, a targeted attempt to fake a "PS ready" signal;
     no effect on `pl_clk0`/`pl_resetn0`.
   - `psu_post_config` — the standard post-configuration hook; still no
     `pl_clk0` toggling afterward.
3. **Full `psu_init` HANGS in `psu_pll_init_data` over JTAG.** This is the
   normal, complete PS bring-up sequence (as run by FSBL/PMU firmware); it
   does not complete when driven by hand over the JTAG debugger in this
   flow, confirming the PS clock generators are not a viable dependency for
   a JTAG-only harness.
4. **Conclusion:** PS-BD clocking (`pl_clk0`/`pl_resetn0`) is unusable for
   JTAG-only bring-up on KV260. The required clocking source is
   **free-running `CFGMCLK`** — the same pattern the rv32 build already
   uses (`generate_rv32_vhdl.shs` / `build_k26_rv32.shs`). Any new PS-BD
   design on this board should default to CFGMCLK from day one rather than
   rediscovering this via a failed `pl_clk0` bring-up.

### Fabric-internal visibility (netlist ILA insertion)

The project-flow ILA knob in `build_k26_rv64.shs`
(`ENABLE_UART_ILA`/`ila_*`) was found to be **dead code** — set but never
consumed, no `create_debug_core` call anywhere — and has been deleted rather
than wired up. The recipe that actually gave fabric-internal visibility on
this board works at the **netlist level, post-route**, and is now scripted
in `scripts/fpga/insert_ila_netlist.tcl`:

1. Open the **`impl_1` ROUTED checkpoint** (`*_routed.dcp`), not the
   `synth_1` DCP — the synth_1 checkpoint for a design with a Zynq PS
   out-of-context (OOC) block design **fails DRC rule INBB-3
   (instantiated black box)** when opened standalone, because the PS BD
   only resolves after place/route pulls the OOC netlist back in.
2. `create_debug_core u_ila_0 ila`; set `C_DATA_DEPTH` etc.
3. `connect_debug_port u_ila_0/clk <clk net>`.
4. Set probe width and `connect_debug_port u_ila_0/probe0 [get_nets
   -hierarchical -filter {MARK_DEBUG}]` (or an explicit net list).
5. `implement_debug_core`; `place_design`; `route_design`;
   `write_bitstream` + `write_debug_probes`.

Runtime: ~15 minutes on this design. This is how the "clk_core never
toggles" finding above was proven, and how BRAM ROM contents can be checked
directly in a checkpoint (loop `get_property INIT_00..INIT_3F` on
`[get_cells -hierarchical -filter {PRIMITIVE_TYPE =~ BLOCKRAM.BRAM.*}]` and
count non-zero INIT strings — distinguishes a populated ROM from a failed
file-based ROM init that left everything zero).

**Read-only-tap limitation:** the `uart_bscan_log` tap is READ-ONLY (TDI is
ignored). All-zero reads over this tap **cannot distinguish a dead tap from
a live tap with no data** — clean, stable zeros (vs. floating/toggling FFs)
are only weak evidence of "alive." This is a diagnosability gap, not
something to fix mid-flight (a build was in flight when this was found): a
future revision should add an always-running, clock-domain aliveness
counter into the capture word so a live tap is unambiguous even with no
payload data. Filed as an improvement note in the bug doc above, not
implemented now.

## Sim gates (run before any board claim)

- `scripts/fpga/ghdl_validate_jtag_debug.shs` → `SOC JTAG DEBUG: ALL PASS`
  (raw JTAG halt/regs/step against the real rv32 hart, TCK = clk/8 through
  the 2-phase tck→clk CDC).
- `scripts/fpga/ghdl_validate_bscan_tunnel.shs` → tunnel self-consistency.
- `scripts/check/check-riscv-hardware-gates.shs` → JTAG VHDL tbs + the
  link_mux probes (`frame`/`mux`/`jtag_route` both modes,
  `link_mux_jtag_debug` interpreter-only).

## Troubleshooting / landmines

| Symptom | Cause / fix |
|---------|-------------|
| OpenOCD `unable to open ftdi device: -3` | Use the Vivado hw_server path for programming; for OpenOCD kill hw_server first (single-client) |
| `pgrep`/`pkill` for vivado/openocd matches itself | Agent shells embed the pattern — use `ps aux \| grep '[l]nx64.o/vivado'` bracket trick |
| `simple compile --backend=vhdl` forks endlessly | CLI self-delegation fork bomb — wrapper guard in `bin/release/simple`; bug doc `cli_compile_delegation_fork_bomb_wrapper_2026-07-24.md` |
| `bin/simple run` HIR "unresolved name" on `std.hardware.*` | Delegate to seed: `SIMPLE_BOOTSTRAP_DRIVER=$PWD/src/compiler_rust/target/bootstrap/simple`; bug doc `native_cli_run_std_hardware_brace_import_unresolved_2026-07-24.md` |
| Model probes fail under JIT | rv64 core model is interpreter-only (`SIMPLE_EXECUTION_MODE=interpreter`) |
| `hart.soc.core.pc = x` rejected | Interpreter refuses >2-level nested field ASSIGNMENT — level-by-level read-modify-writeback (reads are fine) |
| Silent serial log | Identify the fabric UART tty first (`probe_kv260_ps_uart_jtag.shs`); PL UART needs the PMOD adapter |
| Detached waiters never fire | Prefer synchronous `wait_on_run` / in-loop polling over detached notify chains |
| Fabric silent, `pl_clk0`/`pl_resetn0` design | PS never boots in JTAG-only bring-up → `pl_clk0` gated off, `pl_resetn0` held low; use free-running CFGMCLK instead (see "PS-clocked designs on KV260" above) |
| `psu_init` hangs over JTAG | Expected — full PS bring-up cannot complete without FSBL/PMU firmware; do not depend on PS clocking for a JTAG-only flow |
| Need to see fabric-internal signals (no PS, no working UART) | Netlist ILA insertion on the routed checkpoint — `scripts/fpga/insert_ila_netlist.tcl` |
| `uart_bscan_log` reads all zero | Read-only tap; zero cannot distinguish dead tap from live-but-idle tap — treat as inconclusive, not proof of failure |

## References

- Plan + board status: `doc/03_plan/hardware/riscv/fpga_board_bringup_jtag_10min_plan_2026-07-24.md`
- OpenOCD/GDB sim harnesses: `src/lib/hardware/debug/openocd_attach.md`, `gdb_e2e.md`
- Feature expert wiki: `doc/00_llm_process/feature_expert/riscv_soc_linux/skill.md`
- Board bring-up: `kria_k26_fpga_bringup.md`, `kria_k26_ml_carrier_bringup.md`
