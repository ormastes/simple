# OpenOCD BSCAN tunnel framing incompatible with `bscane2_tap_bridge` v1

- **Date:** 2026-07-24
- **Severity:** medium (blocks the OpenOCD attach path; a working
  Vivado `hw_jtag` raw path exists and is board-proven)
- **Status:** open (design gap, not a regression)

## Finding

OpenOCD 0.12's RISC-V BSCAN tunnel (`riscv use_bscan_tunnel <irlen> <type>`,
type 1 = DATA_REGISTER) cannot drive our FPGA-side de-framer
`src/lib/hardware/debug/bscane2_tap_bridge.vhd`. The two framings are mutually
exclusive:

- **Bridge v1** (from the RTL + `tb_bscane2_bridge.vhd`): the USER4 DR stream
  is unbounded 2-bit pairs — bit0 = inner **TMS**, bit1 = inner **TDI**, one
  inner TCK per pair; CAPTURE-DR re-aligns phase; TDO returns LSB-first with
  1 inner-step latency. The **host** walks the inner TAP through every state.
- **OpenOCD** emits `[control][7-bit width=N][N+1 data][control]` and expects
  the **FPGA tunnel FSM** to generate inner TMS. Neither NESTED_TAP (0) nor
  DATA_REGISTER (1) ever emits per-inner-TCK TMS.

A tcl shim cannot fix it — the tunnel payload is built in compiled C. Secondary
defect in the original `scripts/fpga/openocd_kv260_bscan.cfg`: it modeled one
`irlen 12` tap, but the verified chain is two taps (ARM DAP irlen 4 + PL USER4
host).

## Resolution / options

- **In use (board-proven):** Vivado `hw_jtag` raw mode driving the v1 pairs
  directly — see `doc/07_guide/hardware/fpga/simple_riscv_jtag_debugging.md`
  "Board-proven attach recipe". This is how the 2026-07-24 981 s soak PASS was
  read out.
- **Raw-PMOD OpenOCD** (`scripts/fpga/openocd_kv260_pmod_raw.cfg`): stock
  `ftdi` to the bridge's raw tck/tms/tdi/tdo pins — works once a 3.3 V PMOD
  adapter is wired (same hardware gap as the fabric UART).
- **Make the tunnel OpenOCD-compatible (optional):** port SiFive's
  `bscan_tunnel.v` framing FSM into the bridge. Deferred — the exact field bit
  order isn't extractable from the stripped `/usr/bin/openocd`; a blind RTL
  diff risks a wrong bit order. Analysis + per-field evidence archived under
  the session scratchpad `openocd_interop/`.
