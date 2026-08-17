# KV260 rv32 soak: fabric UART (H12/PMOD J2) not routed to any host tty — "0x7EB5A8A9 golden on ttyUSB2" is a false premise

- **Date:** 2026-07-25
- **Severity:** medium (blocks on-silicon observation of the rv32 soak; risks
  false-green if a sim value is reported as board-captured evidence)
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  core-not-running defect)
- **Component:** `build/fpga/evidence/rv32_2026-07-24/rv32_fpga.bit`,
  `scripts/fpga/k26_rv64.xdc`, `scripts/fpga/soak_rv32_board.shs`

## Symptom as reported (and why it is a misattribution)

A debug premise circulated that the golden rv32 soak emitted `0x7EB5A8A9` plus
periodic `P` markers (~24 s) on the fabric UART `/dev/ttyUSB2` on 2026-07-24, and
that "today" (2026-07-25) a clean reconfiguration produced **zero bytes**
(`bytes=0 Pmarkers=0 DONE=NONE`) — implying a same-day regression.

**There is no regression. The board never emitted on ttyUSB2.** Verified this
session:

- `build/fpga/evidence/rv32_2026-07-24/BLOCKER_uart_wiring.txt` (written on the
  golden day) states: *"Preflight capture (program + 65 s while core running):
  0 bytes on BOTH ttys."* The golden-day board capture was already 0 bytes.
- The `0x7EB5A8A9` value is a **host computation**, not a silicon capture:
  `step1_validation.txt` says `Board payload host_golden(260e6)=7EB5A8A9`, and
  the GHDL soak (`ghdl_soak_90000.log`) golden was `A77902FA`. Both are host/sim
  numbers. No `*.raw` under `build/fpga/jtag_debug/` or the golden `jtag/` dir
  has >0 bytes.

## Root cause (electrical routing, verified)

`k26_rv64.xdc` places `uart_tx` on **FPGA pin H12 = KV260 PMOD J2** (SOM240 d18),
`uart_rx` on E10. The KV260 ML carrier does **not** route any PL pin to the
onboard FT4232H. FT4232H channel map (from the BLOCKER note): Ch.A = JTAG,
Ch.B = PS UART1 (`ttyUSB1`), Ch.C = not routed, Ch.D = spare (`ttyUSB2`).
`ttyUSB2` is the spare PS-side channel and is **not electrically connected to the
PL uart_tx pin**. Therefore `ttyUSB2` reads 0 bytes whether or not the soft-core
executes. Confirmed again 2026-07-25: fresh `fpga` reprogram of the golden bit
via hw_server, 120 s capture on `ttyUSB2` at 115200 8N1 = **0 bytes**.

## Is the core actually running?

Almost certainly yes — and independent of the PS. The golden RTL
(`rtl_snapshot/soc_top_rv32.vhd`) clocks off the **STARTUPE3 CFGMCLK** internal
oscillator (~50 MHz) divided by 2 via `BUFGCE_DIV` = ~25 MHz core clock, with no
`pl_clk0`/PS dependency (chosen precisely because pl_clk0 "never toggles under
JTAG-only bring-up"). Reset self-releases after `RESET_RELEASE_COUNT=255` core
cycles (`rst_q <= '0'`). Timing met (WNS +16.588 ns, WHS +0.095 ns). Config is
present (PCAP_STATUS `0x80000FD2`, End-of-startup HIGH). The PS being stuck in a
U-Boot PXE-netboot loop is irrelevant to this core.

**But liveness cannot be positively read on silicon:** the only debug path is the
custom BSCANE2 Simple-TAP (IDCODE 0x15350067), which OpenOCD cannot drive
(`openocd_bscan_tunnel_incompatible_with_v1_bridge_2026-07-24.md`, all-ones on
the raw chain) and which Xilinx xsdb cannot tunnel to (raw chain shows only
`xck26 04724093` + `arm_dap 5ba00477`; no Xilinx debug hub). So there is no
in-band way to read PC/GPRs on the board.

## Fix options (all require hardware access or resynthesis — none applied here)

1. **Wire an external 3.3 V USB-UART adapter to PMOD J2** (TX=H12, RX=E10, GND).
   This is the intended path (unchecked item in
   `doc/07_guide/hardware/fpga/kria_k26_fpga_bringup.md`). Requires physical
   access; no code change. Preferred — keeps the design as-is.
2. **Bridge PL uart_tx to the PS console via EMIO** and echo it out `ttyUSB1`, or
   route the soak progress/golden register out the BSCANE2 Simple-TAP with a
   host-side de-framer that matches bridge v1. Both need an RTL/BD change + PS
   software + **resynthesis** (not run here per session memory constraint).

## Guardrail

Any rv32-board soak report MUST label `0x7EB5A8A9`/`A77902FA` as
**host/GHDL-simulated**, not board-captured, until option 1 or 2 lands. A
`bytes=0` ttyUSB2 capture is the expected (blocked) state, not evidence of a
core stall.
