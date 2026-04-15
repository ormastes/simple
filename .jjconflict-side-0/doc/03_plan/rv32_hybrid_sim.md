# RV32 Hybrid Simulator — Implementation Plan

**Date:** 2026-03-27
**Status:** Draft
**Requirement:** [doc/02_requirements/feature/rv32_hybrid_sim.md](requirements/rv32_hybrid_sim.md)
**Research:** [RTL Simulation](../research/rtl_simulation_riscv32_research.md), [Cosimulation](../research/cosimulation_hybrid_simulation_research.md)

## Objective

Build a three-tier RV32 simulation stack around the existing fast `mllvm_qemu_rtl`
path:

- Tier 1 fast functional execution for boot and throughput
- Tier 2 timing overlay for approximate cycles and hazards
- Tier 3 RTL simulation for signal-level visibility and narrow regions of interest

The critical planning change is this: Tier 3 starts with a native in-process RTL
simulator, not an immediate Verilator dependency. Verilator remains the main
future compatibility target once the internal contracts are stable.

## Architecture Direction

### Core Decisions

- Keep the current fast simulator as the source of truth for broad execution.
- Add timing as an overlay, not by mutating existing IR instruction objects.
- Add native RTL simulation as a Simple-owned engine with a constrained
  synthesizable subset.
- Define a backend boundary early so native RTL and later Verilator backends
  share the same control surface.
- Use tandem retirement traces to validate correctness across mode switches.

### Proposed Capsules

- `mllvm_qemu.timing`
- `mllvm_qemu.trace`
- `mllvm_qemu.rtl_types`
- `mllvm_qemu.rtl_frontend`
- `mllvm_qemu.rtl_sim`
- `mllvm_qemu.sim_bridge`
- `mllvm_qemu.rtl_verilator` later, after native backend stabilization

## Workstreams

### W1: Timing Overlay

Goal: add useful timing before any RTL dependency exists.

Tasks:
- define `TimingAnnotation`, `LatencyTable`, hazard records, and branch/cache
  penalty hooks
- add cycle accounting alongside translation-block execution
- support branch mispredict penalties and a simple L1 hit/miss model
- expose cycle, IPC, and hazard summaries from the runtime

Exit criteria:
- timing mode runs existing RV32 examples
- cycle estimates are within the requirement target

### W2: Native RTL Simulator

Goal: own a deterministic RTL execution engine inside Simple.

Tasks:
- define elaborated nets, registers, memories, ports, and processes
- implement scheduler phases: combinational settle, edge sample, sequential
  update, trace emit
- support one clock domain first
- add VCD dumping and hierarchical signal lookup

Exit criteria:
- the simulator can execute a small synchronous RTL subset
- GTKWave can load produced traces

### W3: RV32 RTL Adapter

Goal: connect architectural CPU state and memory traffic to the RTL simulator.

Tasks:
- define `RtlBackend` and `RtlCoreAdapter`
- map `pc`, GPRs, CSRs, fetch/decode visibility, and memory transactions
- support checkpoint load from fast mode into RTL-visible state
- start with a minimal RV32I pipeline fragment or simple core profile

Exit criteria:
- fast-to-RTL switch can replay a narrow region with consistent visible state

### W4: Tandem Verification

Goal: catch divergence quickly instead of debugging whole traces manually.

Tasks:
- emit retirement traces from fast and RTL modes
- compare PC, instruction, register writeback, and exception outcomes
- stop at first divergence and dump the relevant architectural window

Exit criteria:
- a mismatch is reported at the first divergent retired instruction

### W5: Hybrid Cosimulation

Goal: use fast execution broadly while running selected devices or regions in RTL.

Tasks:
- add MMIO region mapping to an RTL backend
- use bridge hooks at memory access boundaries
- preserve timing synchronization between CPU-side progress and device cycles
- start with a UART-style peripheral before full core switching

Exit criteria:
- a fast CPU can drive at least one RTL-backed peripheral end to end

### W6: External RTL Backend

Goal: keep a path open to Verilator without blocking early delivery.

Tasks:
- stabilize `RtlBackend` APIs against the native backend first
- define a narrow external bridge for clock, reset, poke/peek, and trace
- prototype a Verilator backend only after native tests exist

Exit criteria:
- external backend work is optional and does not reshape earlier phases

## Milestones

### M1: Timing Mode

- timing annotations and CPI model
- hazard and branch reports
- no RTL yet

### M2: Native RTL MVP

- RTL elaboration model
- deterministic stepping
- VCD output

### M3: RV32 Adapter

- checkpoint import
- architectural state mapping
- single-core narrow ROI replay

### M4: Hybrid Peripheral Cosim

- MMIO region mapping
- fast CPU plus RTL peripheral execution

### M5: Tandem Validation

- retirement trace compare
- first-divergence diagnostics

### M6: Optional Verilator Backend

- compatibility proof against `RtlBackend`
- only after native flow is stable

## Recommended Delivery Order

1. Implement W1 fully.
2. Build W2 with tiny hand-authored RTL examples, not a whole RV32 core first.
3. Add W4 early enough to validate W3 as soon as state bridging appears.
4. Start W5 with peripheral cosimulation before whole-core mode switching.
5. Defer W6 until the native simulator contracts stop moving.

## Risks

- Whole-core RTL too early will bury the project in integration work before the
  contracts are clear.
- Verilator-first design would force external-tool assumptions into the core API
  too soon.
- Checkpoint accuracy is easy to underestimate; memory and CSR fidelity need
  explicit tests.
- Timing models can look plausible while being wrong, so trace-based validation
  must arrive before broad rollout.

## Immediate Next Steps

- create the `mllvm_qemu.timing` and `mllvm_qemu.trace` capsules
- define the `RtlBackend` interface and native scheduler contract
- build a tiny RTL smoke example with registers, combinational logic, and VCD
- add a checkpoint schema for `pc`, 32 GPRs, key CSRs, and memory slices
