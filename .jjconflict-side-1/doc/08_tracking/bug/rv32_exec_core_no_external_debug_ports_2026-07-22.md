# rv32_exec_core lacks external hart-debug ports (halt / imem / full GPR)

- **Filed:** 2026-07-22 (Lane EE — JTAG hart-into-core integration)
- **Component:** `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd`
- **Severity:** enhancement / cross-lane request (does NOT block the tb gate)
- **Status:** PARTIALLY RESOLVED (Lane KK, 2026-07-22) — **Gap 3 CLOSED**
  (full x0..x31 readback + full-width pc via 3 additive ports); Gap 1 (halt
  port) and Gap 2 (SBA-into-fetch) remain OPEN. See Resolution below.

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

## Gap 3 — Only x1/x2/x10 + pc exposed for readback — **RESOLVED (Lane KK)**
The core previously exposed `debug_ra` (x1, 16b), `debug_sp` (x2, 16b),
`debug_a0` (x10, 8b) and `debug_pc` (16b) — not the full `regs_q` array, and pc
truncated to 16 bits.
- **FIXED** by 3 ADDITIVE ports on `rv32_exec_core` (safe input default; outputs
  are pure read-only combinational taps of `regs_q` / `pc_q`, add no state and
  cannot perturb execution):
  - `dbg_reg_addr : in std_logic_vector(4 downto 0) := (others => '0')`
  - `dbg_reg_data : out std_logic_vector(31 downto 0)` — full 32-bit value of x[dbg_reg_addr]
  - `dbg_pc       : out std_logic_vector(31 downto 0)` — full-width pc
- `hart_core_glue` now drives `dbg_reg_addr <= gpr_regno` and returns
  `c_dbg_reg_data` for ALL regnos in the abstract-command bridge, and feeds the
  DM's `pc_i`/dpc from the full-width pc.
- **Evidence:** `tb_hart_integration` STAGE D+ sweeps the FULL x0..x31 via
  abstract command (x0=0 hardwired, x1=7, x10=42, all others 0) and STAGE B
  asserts dpc bit31 set (real 0x8000_00xx pc, unreachable via the old 16-bit
  slice). `JTAG HART E2E: ALL PASS`. Native OpenOCD+GDB against the REAL hart
  (`run_native_gdb_hart.shs`): `info registers` shows the real committed regfile
  (a0=42, ra=7) and hardware single-step advances pc 0x8000_0004 -> 0x8000_0008.

## Resolution status (Lane KK, 2026-07-22)
- **Gap 3 — CLOSED.** 3 additive read ports landed on the core; full x0..x31 +
  full-width pc readback proven end-to-end (tb + native GDB). The mandatory
  fail-closed gate held: the GHDL boot proof (real SimpleOS RV32 serial-shell
  banner, 229 UART bytes) is **byte-identical** before vs after the port
  addition (same sha256), confirming the additive ports change no behavior.
- **Gap 1 — OPEN.** No `halt_i`/`clk_en_i` added; `hart_core_glue` still
  clock-gates the core. Left as filed (out of Lane KK scope; not required for
  full-regfile readback).
- **Gap 2 — OPEN, and now empirically confirmed as the breakpoint blocker.**
  GDB's RISC-V single-step / software breakpoints are breakpoint-based: GDB
  plants an ebreak at next-pc via a memory write, which the DM routes over SBA
  to the wrapper's `sba_test_mem` — a memory DISTINCT from the core's internal
  fetch ROM. Native `stepi`/`break` therefore fail with "Failed to read
  original instruction at 0x8000000a / can't add breakpoint" (captured in the
  `run_native_gdb_hart.shs` transcript). Fixing this needs the core's code ROM
  to become a writable RAM fed by an external (SBA) write port — core surgery,
  filed here, deliberately NOT done. Hardware single-step via the monitor
  channel (dcsr.step) is unaffected and fully works on the real hart.
