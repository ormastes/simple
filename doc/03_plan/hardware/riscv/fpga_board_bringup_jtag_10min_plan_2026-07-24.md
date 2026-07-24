# RV32/RV64 Real-FPGA Bring-Up + Simple-JTAG Debug + 10-Minute Soak — Campaign Plan

Date: 2026-07-24
Status: **ACTIVE** — supersedes the board-execution portion of
`riscv32_riscv64_fpga_simpleos_production.md` (whose evidence rules remain
binding). Related: `rv64_fpga_synthesis_plan_2026-07-22.md`,
`rv32_rv64_unification_plan_2026-07-21.md`.

## Goal

1. **RV32 on the real KV260**: re-synthesize the fixed `rv32_exec_core.vhd`,
   program the board over JTAG, and run the Adler-32 hard-job soak for **≥ 10
   minutes wall-clock on the board** with a board-origin UART transcript whose
   `DONE=<golden>~` matches the host reference.
2. **RV64 on the real KV260**: close the honest blocker (no synthesizable RV64
   core exists) far enough to run the same class of 10-minute soak on the
   board, RV64IM subset first (no MMU needed for the soak payload).
3. **Debug via the Simple RISC-V JTAG implementation** (the in-repo
   `jtag_tap.vhd` → `riscv_dtm.vhd` → `dmi_bus.vhd` → `riscv_debug_module.vhd`
   stack), attached from the host through OpenOCD — used as the actual debug
   tool whenever a board run misbehaves, with a captured halt/regs/step
   transcript as evidence.

## Verified Environment (2026-07-24 recon)

| Item | State |
|------|-------|
| Board link | FT4232H (0403:6011) on USB bus path `3-2`; iface 0 (JTAG) unbound/free; ifaces 1.1/1.3 → `/dev/ttyUSB1`,`/dev/ttyUSB2` (user in `dialout`) |
| Programmer | Vivado 2025.2 `~/Xilinx/2025.2/Vivado/bin/vivado` via `scripts/fpga/program_kv260_bitstream.shs` (`connect_hw_server -allow_non_jtag`) — the proven path. `openFPGALoader` direct-ftdi gets LIBUSB access -3; do not fight it, use hw_server |
| RV32 RTL | `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd` — GHDL-clean, 10-min GHDL soak PASS (golden 61F1C501), **DIV overflow guard fixed 2026-07-23** |
| RV32 bitstream | `build/fpga/k26_rv32/**/soc_top_rv32.bit` — **STALE** (predates the DIV fix) → must re-synth |
| RV64 RTL | **NONE synthesizable.** `generate_rv64_vhdl.shs` = BLOCKED: `rv64_vhdl_driver.spl` imports phantom `compile_to_vhdl_module` (defined nowhere). `.spl` behavioral model (`src/lib/hardware/rv64gc_rtl/`) is the oracle, interp-only |
| JTAG debug IP | `src/lib/hardware/debug/`: TAP, DTM, DMI, DM, hart glue + testbenches + `openocd_riscv_sim.cfg`, `run_gdb_e2e.shs` — sim-proven, not yet board-proven |
| Link mux | `src/lib/hardware/link_mux/` frame.spl (COBS+CRC16, probe PASS) + jtag_route.spl — Phase 1 landed |

## Non-Negotiable Evidence Rules (carried forward)

- Board claims need: board identity + programming transcript + serial/JTAG
  transcript, timestamped. Simulation, ILA, or old logs never substitute.
- No stub/fallback PASS. Missing tool/hardware ⇒ `BLOCKED` with the exact
  reason, never a green.
- RV32 and RV64 status are independent.
- A 10-minute soak PASS requires: ≥600 s wall on the DUT, progress markers
  throughout, final `DONE=<8-hex>~` equal to the host-computed Adler-32.

## Lanes (parallel, Opus workers; Fable reviews and lands every diff)

### Lane A — RV32 board run (synth → program → 10-min soak)
1. `sh scripts/fpga/ghdl_validate_rv32.shs` — RTL still clean after DIV fix.
2. Re-synthesize with `scripts/fpga/build_k26_rv32.shs`. **Exactly one Vivado
   at a time** repo-wide (`pgrep -fc 'lnx64.o/vivado'` must be 0 before
   starting; Vivado oversubscription thrashes to ~1 % CPU).
3. Program via `scripts/fpga/program_kv260_bitstream.shs`; capture UART with
   `program_kv260_with_uart_capture.shs` / `kria_uart_check_sample.shs`.
4. Build soak payload + host golden with `scripts/fpga/soak_rv32_hard_job.shs`
   sized for ≥10 min at board clock; run on board; capture serial transcript;
   compare goldens. Evidence under `build/fpga/evidence/` (NOT committed).
5. On any mismatch/hang → hand to Lane B's JTAG attach for live debug.

### Lane B — Simple-JTAG on the board
1. Sim gate first: `run_hart_e2e.shs` / `run_gdb_e2e.shs` green.
2. Integrate the debug stack into `soc_top_rv32.vhd` behind a generate-guard
   config (mirror `SocTopConfig.has_uart` style). Preferred transport:
   **BSCANE2 tunnel** (OpenOCD FTDI + Xilinx BSCAN JTAG tunnel) — zero extra
   cabling, shares the FT4232H chain; PMOD bitbang is the fallback.
3. OpenOCD attach → halt → read PC/GPRs → hw/sw breakpoint → single-step →
   resume; transcript saved. This is the board debug tool for Lanes A/C.
4. Serialize chain users: programming (hw_server) and OpenOCD never overlap.

### Lane C — RV64 synthesizable core (the long pole)
1. Route decision recorded here: **hand-written synthesizable
   `rv64_exec_core.vhd` (RV64IM+Zicsr subset)** extending the proven
   `rv32_exec_core.vhd` structure — NOT the phantom `.spl`→VHDL emitter path
   (no backend exists; do not stub one). The `.spl` model
   (`rv64gc_rtl/core.spl`) is the differential oracle via `difftest_isa.shs`.
2. Gate ladder: GHDL analyze clean → `tb_rv64_wb_soc_smoke.vhd` PASS →
   difftest vs the `.spl` model on the soak instruction mix → GHDL 10-min soak
   golden → synth `build_k26_rv64.shs` + `k26_rv64.xdc` → program → board
   10-min soak (same evidence bar as Lane A).
3. `generate_rv64_vhdl.shs` stays BLOCKED-honest until a real emitter exists;
   update its status text to point at the hand-written core once landed.

## Serialization & Landmines

- **Vivado**: one build at a time (lockfile `build/fpga/.vivado.lock` +
  `pgrep` check). Lane A synth first; Lane C reaches synth much later.
- **JTAG chain**: one client at a time (hw_server programming ⊕ OpenOCD).
- **earlyoom** kills processes named `simple` — long `.spl` runs must copy the
  binary to a scratch name first.
- `.spl` rv64 core model is **interpreter-only** (seed JIT mis-executes it and
  `spl_f64_to_bits`); never "fix" the bare `len()`/imports that force the safe
  fallback.
- Serial capture: `/dev/ttyUSB1`/`/dev/ttyUSB2` — identify which channel is
  the fabric UART with `probe_kv260_ps_uart_jtag.shs` before trusting a
  silent log.
- Evidence/report files stay out of git; plan/doc updates and code land on
  `main` via jj (no branches), SSH key `~/.ssh/id_ed25519_this_mac`.

## Status 2026-07-24 (Lanes A + B executed — RV32 board soak PASS)

- RV32 re-synth **PASS** (Lane A): DIV-fixed core, timing MET, board programmed
  clean. The UART soak was blocked (KV260 carrier routes NO FT4232H channel to
  PL pins; fabric UART on PMOD J2 needs a 3.3 V adapter that is absent) — so the
  soak was taken **cable-free over Simple's own JTAG** instead (Lane B).
- **10-min board soak PASS via Simple JTAG** (Lane B, 2026-07-24 03:50→04:06):
  a debug bitstream (`soc_top_rv32` `G_DEBUG_JTAG=true`, BSCANE2 USER4 tunnel →
  bridge → CDC → Simple TAP/DTM/DMI → DM → rv32 hart; routed timing MET, WNS
  +15.68 ns; soak payload COUNT=260 M baked into ROM) was programmed, then the
  running soak was read out over JTAG: 30 samples of halt→read x18(progress)+
  x8(Adler-32)→resume. **wall = 981 s, x18 strictly monotonic (→0x0F7F4900),
  final x8 = 0x7EB5A8A9 == host golden.** Inner TAP IDCODE 0x15350067 confirmed
  through the tunnel. Key calibration: **TCK = 1 MHz** (bridge CDC proven at
  ≤ core_clk/8 ≈ 3 MHz; the ~15 MHz `hw_jtag` default read all-zeros).
  Attach = Vivado `hw_jtag` raw mode (OpenOCD's tunnel framing is structurally
  incompatible with the v1 bridge — see the interop bug doc). Evidence +
  verdict: `build/fpga/evidence/rv32_2026-07-24/jtag/` (uncommitted).

## Exit Criteria

- [x] RV32: board-origin 10-min soak, golden match, fresh bitstream hash
      recorded — **PASS via Simple JTAG** (981 s, x8 == 0x7EB5A8A9), 2026-07-24.
- [x] JTAG: board-origin halt/read-regs/resume through the Simple TAP/DTM/DM —
      **PASS** (BSCANE2 tunnel, IDCODE 0x15350067, DMI + abstract GPR reads on
      the real hart).
- [x] RV64: board-origin 10-min soak, golden match — **PASS 2026-07-24**
      (wall 616 s, byte_cnt strictly monotonic 4→34 across 35 JTAG samples,
      `DONE=1110197F~` decoded from the BSCANE2 UART-log tap == host Adler-32
      golden for COUNT=100M). Evidence:
      `build/fpga/evidence/rv64_2026-07-24/` (uncommitted).
- [ ] JTAG: board-origin OpenOCD halt/regs/step transcript through the Simple
      TAP/DTM/DM (rv32 satisfied this via Vivado hw_jtag raw mode; the
      OpenOCD-specific path stays blocked on the tunnel-framing interop bug).

## RV64 board result 2026-07-24 (Builds #1–#3)

- Build #1 (PS pl_clk0 @100 MHz): bitgen OK, timing FAILED (WNS −3.758 ns on
  the 64-bit register-file paths). Fixed forward with BUFGCE_DIV /2.
- Build #2 (50 MHz): timing MET (WNS +1.420 ns) — but the board sat silent:
  **KV260 PS never boots in JTAG-only bring-up** (A53s in POR), so pl_clk0 is
  gated and pl_resetn0 low; xsdb-side clock/reset pokes brought the registers
  up yet a netlist-inserted ILA proved clk_core still never toggled. Full
  psu_init hangs in psu_pll_init_data over JTAG. See
  `doc/08_tracking/bug/kv260_ps_bd_pl_clk0_unreachable_jtag_bringup_2026-07-24.md`.
- Build #3 (CFGMCLK free-running clocking, PS BD dropped, COUNT=100M):
  **board soak PASS** — first 'P' markers within seconds of configuration,
  616 s wall, `DONE=1110197F~` == host golden. Read out entirely over the new
  always-on BSCANE2 USER4 UART-log tap (`uart_bscan_log.vhd`), zero UART
  cabling. Lesson recorded in the JTAG debugging guide: PS-clocked designs
  are unusable for JTAG-only bring-up here — clock from CFGMCLK.
