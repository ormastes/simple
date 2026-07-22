# rv32_exec_core lacks external hart-debug ports (halt / imem / full GPR)

- **Filed:** 2026-07-22 (Lane EE — JTAG hart-into-core integration)
- **Component:** `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd`
- **Severity:** enhancement / cross-lane request (does NOT block the tb gate)
- **Status:** OPEN

## Context
Lane EE integrated the REAL `rv32_exec_core` behind the landed
`riscv_debug_module` via a NEW wrapper `src/lib/hardware/debug/hart_core_glue.vhd`
+ tb `tb_hart_integration.vhd`. The gate (`JTAG HART E2E: ALL PASS`) is GREEN:
halt / resume / single-step / abstract-command GPR readback all act on a
genuinely executing hart. The wrapper was built WITHOUT editing the core (per
lane rule). Three core-side gaps had to be worked around at the wrapper level;
each needs a small, additive core port to be fully faithful. **None require
changing existing core behavior — all are new optional outputs/inputs.**

## Gap 1 — No halt / clock-enable / fetch-stall port
The core entity is only `clk / rst + debug_* outputs`. There is no way to halt
the hart from outside. **Workaround:** the wrapper CLOCK-GATES the core
(`core_clk <= clk and enable`, enable latched on the falling edge so only whole
pulses reach the core). This is functionally correct in simulation and maps to
a clock-enable / BUFGCE on FPGA, but a native `halt_i` / `clk_en_i` input would
be cleaner and avoids gated-clock synthesis constraints on the board.
- **Requested:** add an optional `clk_en_i : in std_logic := '1'` (or
  `halt_i`) that stalls the FSM without gating the clock.

## Gap 2 — No external instruction memory / SBA-into-fetch
The core fetches from an INTERNAL ROM loaded from `rv32_payload.mem` at
elaboration; there is no external instruction-bus port. Therefore the Debug
Module's System Bus Access (SBA) master CANNOT write a program the core will
then fetch and execute. **Workaround:** the wrapper exercises the DM SBA master
against a wrapper-owned `sba_test_mem` (proves the SB path through the glue),
and the hart executes the deterministic baked ROM the harness stages. The
"program load -> hart executes loaded program" chain is therefore split.
- **Requested:** expose an external instruction-fetch port (or a writable code
  RAM with an external write port) so SBA can load the executed program.

## Gap 3 — Only x1/x2/x10 + pc exposed for readback
The core exposes `debug_ra` (x1, 16b), `debug_sp` (x2, 16b), `debug_a0` (x10,
8b) and `debug_pc` (16b) — not the full `regs_q` array, and pc is truncated to
16 bits. **Workaround:** abstract-command GPR readback returns real committed
values for x1/x2/x10 (asserted: x10==42, x1==7 — real program output) and 0 for
other regnos; dpc carries pc's low 16 bits. Arbitrary-GPR readback needs the
core to expose `regs_q` (and full 32-bit pc).
- **Requested:** an optional debug read port
  `dbg_regsel_i / dbg_regval_o` over the full register file, and a full-width
  `debug_pc32`.

## Not editing the core
All three are additive core ports. Per the lane rule ("if a core hook is
unavoidable, STOP and report it as a cross-lane request instead of editing"),
these are filed here rather than patched. The tb gate passes today with the
wrapper-level workarounds documented in `hart_core_glue.vhd`.
