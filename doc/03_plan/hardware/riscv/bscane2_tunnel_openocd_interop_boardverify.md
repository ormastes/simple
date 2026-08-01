# Feature request / board-verify: BSCANE2 tunnel ↔ OpenOCD bit-exact interop

**Status:** OPEN — Phase 3 (board) verification item. Filed by Lane B.
**Area:** `src/lib/hardware/debug/` (JTAG debug), KV260 rv32 SoC.

## What is done (sim-proven, GHDL-08)
- `jtag_debug_chain.vhd` — raw-JTAG → `jtag_tap` → `riscv_dtm` → **tck→clk CDC** →
  `dmi_bus` → `hart_core_glue` (DM + clock-gated **real rv32 hart**). End-to-end
  over the real serial TAP with **TCK 8× slower than core clk**: examine, halt,
  read pc + GPRs, single-step ×2, resume — `tb_soc_jtag_debug` **ALL PASS**
  (`scripts/fpga/ghdl_validate_jtag_debug.shs`).
- `bscane2_tap_bridge.vhd` + `bscane2_stub.vhd` — BSCANE2 USER-tunnel de-frame →
  raw-JTAG replay into the chain. IDCODE round-trips through the tunnel
  self-consistently — `tb_bscane2_bridge` **PASS**
  (`scripts/fpga/ghdl_validate_bscan_tunnel.shs`).
- `soc_top_rv32.vhd` — integration behind `G_DEBUG_JTAG` (default **false**, no
  new top ports; BSCANE2 taps the internal config JTAG).

## The gap (why this is filed, not silently shipped)
The FPGA side implements **"Simple nested-TAP tunnel v1"** (2 outer USER-DR bits
per inner TCK step; see `bscane2_tap_bridge.vhd` header). OpenOCD 0.12's built-in
`riscv use_bscan_tunnel <irlen> {0:NESTED_TAP|1:DATA_REGISTER}` uses its own
DATA_REGISTER framing (documented shape: select-DMI DR = 3 + irlen(5) + 7 + 1
bits, 1-bit start offset, 1-bit TCK skew). **These framings are not yet proven
bit-identical**, and the exact OpenOCD encoding could not be confirmed offline
(WebFetch of `riscv-openocd/.../riscv.c` is blocked in this environment).

## Resolution options (pick at board bring-up)
1. **Match OpenOCD's DATA_REGISTER framing** in `bscane2_tap_bridge.vhd` (adjust
   the de-frame FSM to OpenOCD's exact bit layout), then `riscv use_bscan_tunnel
   5 1` works directly. Preferred once the format is read from OpenOCD source.
2. **Small OpenOCD tcl tunnel shim** that emits the v1 framing (if native tunnel
   can't be matched cheaply).
3. **Raw-JTAG PMOD fallback (VERIFIED, zero tunnel risk):** bring `tck/tms/tdi/
   tdo` to PMOD pins straight into `jtag_debug_chain`; standard OpenOCD `ftdi`
   (3.3V FT2232H). This path reuses the already-verified serial TAP — no tunnel.
   Blocked today only by "no 3.3V adapter cabled to PL PMOD" (Lane A note).

## Acceptance (board evidence bar)
Program the `G_DEBUG_JTAG=true` bitstream, release the JTAG chain (single-client:
kill hw_server / close Vivado), then `scripts/fpga/check_kv260_jtag_debug.shs
verify` PASS + a `soak` run ≥600 s with golden Adler-32 compare — with the
OpenOCD transcript captured. Until that transcript exists, **do not claim OpenOCD
interop**.
