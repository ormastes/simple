# K26 rv32 flow has no timing constraints; core closes ~36.9 MHz, not 100 MHz

**Filed:** 2026-07-22 (lane K, during the BRAM-banking re-synth that produced
the first successful `rv32_fpga.bit`)
**Status:** OPEN
**Severity:** high for on-board correctness claims (bitstream builds, but
timing is unverified by the flow and the core cannot run at 100 MHz)

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
