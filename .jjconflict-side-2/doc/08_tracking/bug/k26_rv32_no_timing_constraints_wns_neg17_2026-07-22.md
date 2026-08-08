# K26 rv32 flow has no timing constraints; core closes ~36.9 MHz, not 100 MHz

**Filed:** 2026-07-22 (lane K, during the BRAM-banking re-synth that produced
the first successful `rv32_fpga.bit`)
**Status:** RESOLVED 2026-07-22 (lane N) — flow now constrains the real clock,
fails closed on WNS/WHS < 0, and the routed design MEETS timing at the real
board clock. Remaining hardware dependency tracked below (PMOD UART adapter).
**Severity:** high for on-board correctness claims (bitstream builds, but
timing is unverified by the flow and the core cannot run at 100 MHz)

## Resolution (lane N, 2026-07-22)
- `soc_top_rv32.vhd` (example template): core domain moved from raw cfgmclk
  (~50 MHz nominal) to `clk_core` = cfgmclk/2 = 25 MHz via `BUFGCE_DIV`
  (BUFGCE_DIVIDE=2); reset counter + marker tracker + core all in clk_core.
- Core instantiated with `CLK_FREQ => 25_000_000, BAUD_RATE => 115_200` so
  `BAUD_DIV = CLK_FREQ/BAUD` matches the real clock (was: 100 MHz default on a
  50 MHz clock → 2x-fast baud).
- XDC now constrains the primitive pin, not a dangling net:
  `create_clock -name cfgmclk -period 20.000 [get_pins u_startup/CFGMCLK]`
  (+ `set_false_path -to [get_ports uart_tx]`); the 25 MHz generated clock is
  auto-derived through BUFGCE_DIV.
- `build_k26_rv32.shs` is fail-closed: after route it reads
  `STATS.WNS`/`STATS.WHS` from impl_1 and refuses to emit the bitstream on any
  negative slack; also gates on a real (non-NOP) `rv32_payload.mem` (missing
  payload .bin used to silently produce a 1-word NOP image = guaranteed
  0 UART bytes) and absolutizes the `rv32_fat32.mem` textio path.
- Routed result (xck26-sfvc784-2lv-c): **WNS +16.932 ns, WHS +0.054 ns,
  pulse-width +18.929 ns, 0 failing endpoints / 10,957** at 25 MHz core /
  50 MHz cfgmclk primary. Utilization: 15,618 CLB LUTs (13.3%), 1,366 CLB
  registers (0.6%), 38 BRAM tiles (26.4%), 10 DSPs.
- Board: bitstream programmed on KV260, `End of startup status: HIGH`
  (DONE=HIGH), PROGRAM_STATUS=ok. Carrier USB UARTs (ttyUSB1/2, PS-side MIO)
  captured 30 s @115200 → 0 bytes, as physically expected: the PL UART drives
  package pin H12 (PMOD), which is NOT wired to the carrier's USB UARTs.
- **Single remaining hardware dependency (NOT a flow bug):** attach a 3.3 V
  TTL USB-UART adapter to the KV260 PMOD (PL uart_tx = package pin H12; board
  RX pin E10 per the existing pin map) to observe the `FPGA-RV32` boot marker
  and SimpleOS output. No board-serial claim is made without captured bytes.

## Facts
- The shipped `build_k26_rv32.shs` flow constrains nothing: routed timing
  report says "There are no user specified timing constraints". The XDC
  dropped `create_clock` expecting PS `pl_clk0` auto-constraints, but the
  actual synthesis top `build/vhdl/rv32/soc_top_rv32.vhd` is clocked from
  STARTUPE3 **cfgmclk** (PS block design is dangling).
- Post-hoc probe on the routed DCP with a 100 MHz clock: **WNS −17.116 ns**
  (9,099 failing endpoints), WHS −0.066 ns → critical path ≈27.1 ns →
  **max ≈36.9 MHz**. Report: `build/fpga/k26_rv32/timing_probe_100mhz.rpt`.
- Cause is the pre-existing single-process decode/execute blob, NOT the
  BRAM banking (banking only registered memory reads).
- Consequence: `CLK_FREQ=100e6`-derived UART baud divisor does not match the
  actual cfgmclk frequency — on-board UART output will be at the wrong baud
  until reconciled.

## Fix directions
1. Constrain the real clock in the XDC (`create_clock` on the cfgmclk path or
   wire the PS `pl_clk0` properly) so the flow FAILS on timing instead of
   silently shipping unverified bitstreams (fail-closed).
2. Either run the core at ≤33 MHz (safe with measured WNS) with a matching
   baud divisor, or pipeline the decode/execute path for 100 MHz.
3. Reconcile CLK_FREQ constant vs the actual board clock for UART.

## Context
First successful K26 placement after
`[Place 30-484] could not place all lutrams` was fixed by replicated-BRAM
banking (rom_a/rom_b + registered single reads, S_FETCH/S_LOAD/S_STORE defer
states). GHDL gate: 297/297 UART bytes bit-identical vs pre-banking core,
ending `TEST PASSED` (transcripts in lane artifacts).
