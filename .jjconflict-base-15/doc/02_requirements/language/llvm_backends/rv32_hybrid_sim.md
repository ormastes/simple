# RV32 Hybrid Simulator — Requirements

**Feature:** `rv32_hybrid_sim`
**Date:** 2026-03-27
**Status:** Draft
**Related:** [Plan](../rv32_hybrid_sim.md), [Research](../../research/rtl_simulation_riscv32_research.md), [Cosim Research](../../research/cosimulation_hybrid_simulation_research.md)

---

## Motivation

The existing `mllvm_qemu_rtl` example has a working fast-mode RV32I emulator (IR_TC decode → optimize → JIT) but lacks:
1. **Timing awareness** — no cycle counts, no pipeline model, no latency information
2. **RTL-level simulation** — no signal types, no clock domains, no waveform output
3. **Mode switching** — no way to transition between fast and cycle-accurate execution

A hybrid simulator enables: fast boot/setup via IR_TC, then switch to timing-approximate or cycle-accurate RTL for the region of interest. This follows the MARSS-RISCV overlay pattern and gem5's fast-forward-to-checkpoint approach.

Research indicates a staged implementation is the only practical path:
- Verilator is the strongest open-source Tier 3 target, but is still orders of magnitude slower than the existing fast simulator
- the first useful milestone is an in-process Simple RTL simulator with waveform support and a narrow executable subset
- external RTL cosimulation should be treated as a later compatibility tier, not the first dependency

---

## Scope

### In Scope

- **REQ-SIM-001**: Timing entity types (`TimingAnnotation`, `LatencyTable`, `PipelineStage`, `CycleCount`)
- **REQ-SIM-002**: 5-stage pipeline overlay model for RV32I (Fetch/Decode/Execute/Memory/Writeback)
- **REQ-SIM-003**: RTL entity types (`Signal`, `SignalValue` with 4-state 0/1/X/Z, `Wire`/`Reg`, `ClockEdge`, `RtlModule`, `RtlPort`)
- **REQ-SIM-004**: RTL simulation engine (`RtlSimEngine`) — cycle-based event-driven evaluation
- **REQ-SIM-004A**: Native RTL elaboration model (`RtlNet`, `RtlProcess`, `RtlInstanceGraph`) for a Simple-defined synthesizable subset
- **REQ-SIM-004B**: Deterministic scheduler ordering for `comb -> edge sample -> seq update -> trace emit`
- **REQ-SIM-005**: Mode switching (`SimModeSwitcher`) — fast <-> timing <-> RTL at TB boundaries
- **REQ-SIM-006**: State snapshot/restore for mode transitions (`StateSnapshot`)
- **REQ-SIM-007**: VCD waveform trace output (`SignalTrace`, `WaveformDumper`)
- **REQ-SIM-008**: MDSOC capsule integration — 5 new capsules, no modification to existing ones
- **REQ-SIM-009**: Primitive timing check — detect hazards, stalls, branch misprediction penalties
- **REQ-SIM-010**: Cosimulation bridge — AOP weaving for memory-mapped fast/RTL boundary
- **REQ-SIM-011**: Instruction retirement trace for tandem checking between fast/timing/RTL modes
- **REQ-SIM-012**: RV32 core adapter boundary that maps architectural CPU state (`pc`, GPRs, CSRs, memory transactions) onto the RTL simulator
- **REQ-SIM-013**: Simulator backend abstraction with at least `NativeRtlBackend` first and `VerilatorBackend` as a later compatible target
- **REQ-SIM-014**: Initial RTL simulator scope restricted to single-clock synchronous modules, combinational logic, registers, memories, and MMIO-ready port wiring

### Out of Scope

- M/A/F/D/C extensions (only base RV32I)
- FPGA-accelerated simulation (FireSim-style)
- Full SystemC/TLM integration
- JIT compilation of RTL (interpret only)
- Multi-core / multi-hart simulation
- Cache hierarchy beyond L1 hit/miss model
- Gate-level timing, SDF back-annotation, or STA replacement
- Full Verilog/SystemVerilog language support in the native simulator

---

## I/O Examples

### Example 1: Fast Mode with Timing Overlay

```simple
# Boot in fast mode, get approximate cycle count
val sim = HybridSimulator(mode: SimMode.TimingApproximate)
sim.load_elf("hello_riscv32.elf")
sim.run_until_pc(0x80000100)
print "Cycles: {sim.cycle_count()}"       # e.g., 847
print "IPC: {sim.ipc()}"                  # e.g., 0.72
print "Branch misses: {sim.branch_misses()}"  # e.g., 12
```

### Example 2: Mode Switching (Fast -> RTL)

```simple
val sim = HybridSimulator(mode: SimMode.Fast)
sim.load_elf("firmware.elf")
# Fast-forward through boot
sim.run_until_pc(0x80001000)
# Switch to RTL for detailed analysis
sim.switch_mode(SimMode.RtlCycleAccurate)
sim.enable_trace("regs.vcd")
sim.run_cycles(1000)
sim.dump_waveform()
# Switch back to fast
sim.switch_mode(SimMode.Fast)
sim.run_until_halt()
```

### Example 3: Pipeline Hazard Detection

```simple
val sim = HybridSimulator(mode: SimMode.TimingApproximate)
sim.load_elf("test.elf")
sim.enable_hazard_report()
sim.run_until_halt()
val report = sim.hazard_report()
for h in report.data_hazards:
    print "Data hazard at PC={h.pc}: {h.src_reg} RAW stall {h.stall_cycles}cy"
for h in report.control_hazards:
    print "Branch mispredict at PC={h.pc}: penalty {h.penalty_cycles}cy"
```

### Example 4: RTL Signal Inspection

```simple
val sim = HybridSimulator(mode: SimMode.RtlCycleAccurate)
sim.load_elf("blinky.elf")
sim.run_cycles(10)
val alu_out = sim.read_signal("cpu.alu_result")
print "ALU output: {alu_out}"  # e.g., SignalValue(0x0000_0042)
val pc_wire = sim.read_signal("cpu.pc")
print "PC: {pc_wire}"          # e.g., SignalValue(0x8000_0010)
```

### Example 5: Cosimulation (Fast CPU + RTL Peripheral)

```simple
val sim = HybridSimulator(mode: SimMode.Fast)
sim.load_elf("uart_test.elf")
# Map UART peripheral (0x10000000-0x10000FFF) to RTL simulation
sim.map_rtl_region(0x10000000, 0x1000, "uart_rtl_module")
sim.run_until_halt()
# Fast CPU + cycle-accurate UART peripheral ran together
print "UART TX bytes: {sim.rtl_region_stats(0x10000000).tx_count}"
```

### Example 6: Native RTL Module Stepping

```simple
val rtl = NativeRtlBackend()
rtl.load_module("rv32_pipeline_core")
rtl.set_clock("clk", period_cycles: 2)
rtl.set_reset("rst_n", active_low: true)
rtl.poke("imem_ready", 1)
rtl.step_cycles(20)
print rtl.peek("pc_q")
print rtl.trace_stats().signal_count
```

---

## Acceptance Criteria

1. **AC-001**: `TimingAnnotation` attaches to IR_TC instructions via parallel map (no modification to `IrTcInst`)
2. **AC-002**: Pipeline overlay produces cycle count within 15% of reference (Spike commit log) for RV32I integer workloads
3. **AC-003**: RTL engine evaluates combinational + sequential logic per clock edge
4. **AC-004**: Mode switch fast->timing completes in <1ms for 42-register state transfer
5. **AC-005**: VCD output is valid and loadable by GTKWave
6. **AC-006**: Hazard report correctly identifies RAW/WAW/WAR data hazards and control hazards
7. **AC-007**: All 5 new MDSOC capsules pass layer checking with no modifications to existing capsules
8. **AC-008**: Cosim bridge intercepts memory accesses to RTL-mapped regions via AOP weaving
9. **AC-009**: All existing `mllvm_qemu_rtl` tests continue to pass (no regression)
10. **AC-010**: Native RTL simulator executes a small synchronous RTL subset without requiring external tools
11. **AC-011**: Tandem trace comparison can detect first divergent retired instruction between fast and RTL execution
12. **AC-012**: Backend boundary is stable enough that a later Verilator driver can reuse the same `RtlBackend` contract

---

## Dependencies

| Module | What We Need | Exists? |
|--------|-------------|---------|
| `mllvm_qemu.core` | IR_TC types, ops, builder | Yes |
| `mllvm_qemu.guest_riscv` | RV32 decoder, CPU def | Yes |
| `mllvm_qemu.runtime` | JitCache, GuestMemory, EmulatorEngine | Yes |
| `mllvm_qemu.opt` | PassManager, TbChain | Yes |
| `85.mdsoc` | VirtualCapsule, LayerChecker, Weaving | Yes |
| `mllvm_qemu.trace` (new) | retirement trace + compare | No |
| `mllvm_qemu.rtl_frontend` (new) | native RTL elaboration/input model | No |
| SFFI (future) | Verilator bridge for optional external backend | Not needed in phase 1 |

---

## Three-Tier Model

| Tier | Entity Types | Feature Capsule | Speed Target |
|------|-------------|----------------|-------------|
| **1 — Fast** | (existing IR_TC) | `mllvm_qemu.runtime` (existing) | 50-200 MIPS |
| **2 — Timing** | `mllvm_qemu.timing` | Pipeline overlay in `mllvm_qemu.runtime` | 5-50 MIPS |
| **3A — Native RTL** | `mllvm_qemu.rtl_types`, `mllvm_qemu.rtl_frontend` | `mllvm_qemu.rtl_sim` | 0.5-5 MIPS |
| **3B — External RTL** | Verilator-compatible bridge types | `mllvm_qemu.rtl_verilator` | 0.5-20 MHz equivalent for narrow DUTs |

**Bridge:** `mllvm_qemu.sim_bridge` (transform) handles all mode transitions.

## Delivery Strategy

### Phase 1: Timing Overlay First

- keep the existing fast RV32 path as the execution authority
- attach timing metadata and branch/cache penalty models in parallel structures
- produce cycle, hazard, and branch statistics without changing `IrTcInst`

### Phase 2: Native RTL Simulator

- add a minimal elaborated RTL object model
- support one clock domain, deterministic scheduling, register transfer, and VCD output
- prove the engine on a tiny RV32 pipeline fragment before integrating a whole core

### Phase 3: Hybrid CPU/Peripheral Cosimulation

- map MMIO regions to the native RTL simulator first
- add checkpoint/restore and retirement-trace comparison
- switch execution granularity at translation-block or explicit ROI boundaries

### Phase 4: Optional External Backend

- reuse the same backend contract for Verilator
- reserve DPI/SFFI bridging for later once the native contracts are stable
- do not block the native simulator on external toolchain integration
