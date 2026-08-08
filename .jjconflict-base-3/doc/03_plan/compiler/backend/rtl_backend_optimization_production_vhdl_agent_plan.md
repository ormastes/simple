# RTL Backend Optimization — Agent Spawn Plan

- **Date:** 2026-06-01
- **Research:** `doc/01_research/hardware/baremetal/simple_rtl_backend_optimization_production_vhdl_2026-06-01.md`
- **Coordination:** Parallel agents with disjoint file scopes. Shared compiler/runtime edits require serialized merges.

---

## Agent Overview

| Agent | Scope | Primary Deliverables | Disjoint Files |
|-------|-------|----------------------|----------------|
| A: HWIR Foundation | New HWIR types + MIR → HWIR lowering | HWIR module, legality checker, HWIR → VHDL bridge | `src/compiler/50.mir/hwir/`, `src/compiler/60.mir_opt/hwir_opt/` (new) |
| B: VHDL Hardening | Production VHDL templates, target profiles | Vendor profiles, DSP/CDC templates, deterministic naming | `src/compiler/70.backend/backend/vhdl/`, `src/compiler/70.backend/backend/vhdl_*` |
| C: RV32 QoR Proof | RV32I core through GHDL + synthesis, QoR comparison | RVFI interface, riscv-formal, PPA reports | `src/lib/hardware/rv32i_rtl/`, `src/lib/hardware/soc_rtl/`, GHDL runners |
| D: RV64 Pipeline | RV64 5-stage pipeline hardening + extension | Pipeline hazards, branch prediction, M/C extension | `src/lib/nogc_sync_mut/hardware/rv64/pipeline/`, `src/lib/hardware/rv64gc_rtl/` |
| E: Toolchain CI | GHDL/Yosys/nextpnr CI lanes | CI workflow, smoke tests, regression gates | `.github/workflows/`, `scripts/rtl/` (new), CI configs |
| F: QoR Database | QoR schema, benchmark harness, autotune | QoR entity store, CLI commands, comparison reports | `src/lib/nogc_sync_mut/hardware/qor/` (new), `src/app/rtl/` (new) |
| G: Debuggability | Source-map enrichment, waveform tooling | HWIR source maps, explain command, first-divergence reports | `src/compiler/80.driver/driver_compile_vhdl_source_map.spl`, `src/compiler/35.semantics/lint/riscv_rtl_debuggability_lint.spl` |

---

## Phase 1 — Foundation (M0 + M1)

### Agent A: HWIR Foundation

**Scope:** Create the hardware IR layer between MIR and VHDL backend.

**File scope (exclusive):**
- `src/compiler/50.mir/hwir/` (new directory)
- `src/compiler/60.mir_opt/hwir_opt/` (new directory)

**Tasks:**
1. Define HWIR types in pure Simple at `src/compiler/50.mir/hwir/types.spl`:
   - `HwModule`, `HwPort`, `HwSignal`, `HwRegister`, `HwCombOp`
   - `HwMemory`, `HwFsm`, `HwPipeline`, `HwClockDomain`, `HwResetPolicy`
   - `HwResourceBinding`, `HwSourceMap`, `HwCostModel`
2. Add MIR → HWIR lowering at `src/compiler/50.mir/hwir/mir_to_hwir.spl`:
   - Lower `MirFunction` → `HwModule` for hardware-tagged functions
   - Preserve the existing `compile_function()` path as fallback
   - Map `MirLocal` kinds to `HwSignal`/`HwRegister` based on clock annotations
3. Add hardware legality checker at `src/compiler/35.semantics/lint/hwir_legality_lint.spl`:
   - Reject: floating point, pointers, dynamic allocation, unbounded loops, multiple drivers
   - Emit stable diagnostic codes: `HWIR-E-FLOAT`, `HWIR-E-PTR`, `HWIR-E-UNBOUNDED`, `HWIR-E-MULTI-DRIVER`, `HWIR-E-COMB-LOOP`
4. Add HWIR → VHDL bridge at `src/compiler/70.backend/backend/hwir_to_vhdl.spl`:
   - Route through existing `VhdlBuilder` for code emission
   - Initially 1:1 translation to match current behavior

**Exit criteria:** MIR → HWIR → VHDL output matches current VHDL for all existing test cases. Legality checker rejects known unsupported constructs with stable diagnostics.

**Dependencies:** None (greenfield).

---

### Agent B: VHDL Hardening

**Scope:** Harden existing VHDL backend for production synthesis across targets.

**File scope (exclusive):**
- `src/compiler/70.backend/backend/vhdl/` (existing files)
- `src/compiler/70.backend/backend/vhdl_*` (existing files)

**Tasks:**
1. Add target profile system at `src/compiler/70.backend/backend/vhdl/vhdl_target_profile.spl`:
   - `generic-vhdl-2008`, `ghdl-yosys`, `vivado`, `quartus`, `yosys-nextpnr`, `openroad-asic`
   - Each profile controls: allowed VHDL constructs, attribute syntax, memory/DSP template style, reset preference
2. Add DSP inference templates at `src/compiler/70.backend/backend/vhdl/vhdl_dsp_templates.spl`:
   - Multiply, multiply-add, multiply-accumulate, dot product patterns
   - DSP vs LUT binding selection
3. Add CDC primitives at `src/compiler/70.backend/backend/vhdl/vhdl_cdc_primitives.spl`:
   - `@cdc_sync`, `@async_fifo`, `@gray_counter`, `@pulse_crossing`
   - Implicit cross-domain signal use → error diagnostic
4. Harden existing memory templates:
   - Add true dual-port RAM, FIFO, register file templates
   - Add vendor-specific inference pragmas (conditional on target profile)
5. Add deterministic naming mode for release builds:
   - Short stable names + external name map
   - Debug mode preserves human-readable names

**Exit criteria:** All existing VHDL tests still pass. New target profiles produce compilable VHDL for at least `ghdl-yosys` and `vivado` profiles. CDC crossings without annotation → error.

**Dependencies:** None (works on existing files).

---

### Agent E: Toolchain CI

**Scope:** Create CI lanes for GHDL/Yosys/nextpnr.

**File scope (exclusive):**
- `.github/workflows/rtl-*.yml` (new)
- `scripts/rtl/` (new directory)

**Tasks:**
1. Create GHDL analysis+elaboration+run CI lane:
   - Use existing GHDL runner scripts as templates
   - Run on all RTL examples in `src/lib/hardware/`
2. Create `ghdl --synth` lane for synthesis validation
3. Create Yosys + ghdl-yosys-plugin lane for open-source synthesis
4. Create nextpnr smoke test (iCE40 or ECP5 target)
5. Add OpenROAD-flow-scripts ASIC smoke test (sky130 PDK)
6. Wire regression policy: determinism check, correctness gate

**Exit criteria:** CI runs on push for `src/lib/hardware/**` changes. At least analysis+elaboration+simulation passes for RV32I core.

**Dependencies:** None (CI infra only).

---

## Phase 2 — Optimization (M2)

### Agent A (continued): HWIR Optimizer

**Tasks:**
1. Add bit-width narrowing at `src/compiler/60.mir_opt/hwir_opt/width_narrowing.spl`:
   - Range inference, operator narrowing, redundant sign/zero extension removal
2. Add structural simplification at `src/compiler/60.mir_opt/hwir_opt/structural_simplify.spl`:
   - Constant fold, dead signal/register elimination, redundant mux removal, CSE
3. Add resource binding at `src/compiler/60.mir_opt/hwir_opt/resource_binding.spl`:
   - `@rtl_profile("area")` → share multipliers, prefer iterative divide
   - `@rtl_profile("speed")` → duplicate critical resources, pipeline long paths
   - `@rtl_profile("balanced")` → target cost model
4. Add FSM optimization at `src/compiler/60.mir_opt/hwir_opt/fsm_opt.spl`:
   - Detect FSMs from state variables, choose encoding, eliminate unreachable states
5. Add memory inference at `src/compiler/60.mir_opt/hwir_opt/memory_inference.spl`:
   - Recognize register file, block/distributed RAM, ROM, FIFO patterns
6. Add DSP inference at `src/compiler/60.mir_opt/hwir_opt/dsp_inference.spl`:
   - Multiply, MAC, dot product, FIR patterns → DSP or LUT binding

**Exit criteria:** Area mode reduces LUT/FF on area fixtures. Speed mode improves Fmax estimate. Each optimization independently disableable.

**Dependencies:** Phase 1 Agent A (HWIR types).

---

## Phase 3 — Proof and QoR (M3 + M4)

### Agent C: RV32 QoR Proof

**Scope:** Push existing RV32I core through formal verification and QoR comparison.

**File scope (exclusive):**
- `src/lib/hardware/rv32i_rtl/` (add RVFI)
- `src/lib/hardware/soc_rtl/` (testbench additions)
- GHDL runner scripts

**Tasks:**
1. Add optional RVFI output port to `rv32i_rtl/core.spl`:
   - `rvfi_valid`, `rvfi_insn`, `rvfi_trap`, register/PC/memory signals
   - Gate behind `@rvfi_enabled` compile-time flag
2. Wire riscv-formal flow:
   - Generate RVFI-connected wrapper for formal tools
   - Run rv32i instruction checks
3. Run riscv-tests ISA test suite through GHDL simulation
4. Collect QoR metrics:
   - GHDL simulation + ghdl-yosys synthesis on iCE40/ECP5/Artix-7
   - Compare LUT/FF/Fmax against PicoRV32 and NEORV32
5. Publish PPA report at `doc/08_tracking/hardware/rv32i_qor_baseline.md`

**Exit criteria:** RV32I formal pass. ISA tests pass. Synthesis succeeds on at least one target. PPA report with competitor baselines.

**Dependencies:** Phase 1 Agent E (CI lanes).

---

### Agent D: RV64 Pipeline Hardening

**Scope:** Harden existing RV64 5-stage pipeline.

**File scope (exclusive):**
- `src/lib/nogc_sync_mut/hardware/rv64/pipeline/`
- `src/lib/hardware/rv64gc_rtl/`

**Tasks:**
1. Add data hazard detection and forwarding:
   - RAW hazard detection in ID/EX stages
   - Forwarding paths (EX→EX, MEM→EX)
   - Load-use stall logic
2. Add branch handling:
   - Branch resolution in EX stage
   - Branch penalty tracking
   - Optional static branch prediction
3. Add M extension pipeline integration:
   - Multi-cycle multiply/divide in EX stage
   - Pipeline stall for long-latency operations
4. Add pipeline performance counters:
   - CPI, branch penalty, stall cycles, forwarding count
5. Run ISA tests through pipeline model

**Exit criteria:** RV64I ISA tests pass through pipeline. Hazards handled correctly. Performance counters report CPI.

**Dependencies:** None (existing files).

---

### Agent F: QoR Database

**Scope:** Build QoR tracking infrastructure.

**File scope (exclusive):**
- `src/lib/nogc_sync_mut/hardware/qor/` (new)
- `src/app/rtl/` (new)

**Tasks:**
1. Define QoR entity schema (MDSOC+ ECS pattern):
   - `RtlQorRun` entity with all metrics
   - `ComponentStore<RtlQorRun>` for in-memory storage
   - SDN file-based persistence
2. Build `simple rtl bench` command:
   - Run GHDL simulation + synthesis for a design
   - Collect metrics into QoR database
3. Build `simple rtl compare` command:
   - Compare two runs or compare against baseline
   - Output table with delta percentages
4. Build `simple rtl qor report` command:
   - Generate HTML or markdown report with charts
5. Add regression detection:
   - Area/Fmax/CoreMark threshold alerts

**Exit criteria:** `simple rtl bench --suite=smoke` produces a QoR report. Comparison against previous run shows deltas.

**Dependencies:** None (greenfield app).

---

### Agent G: Debuggability

**Scope:** Enrich source-map and waveform tooling.

**File scope (exclusive):**
- `src/compiler/80.driver/driver_compile_vhdl_source_map.spl`
- `src/compiler/35.semantics/lint/riscv_rtl_debuggability_lint.spl`

**Tasks:**
1. Extend source map to include HWIR node IDs (when HWIR is available)
2. Add `simple rtl explain --vhdl-line` command:
   - Map VHDL line → HWIR node → Simple source
   - Show optimization decisions that affected the signal
3. Add waveform group generation:
   - Group signals by Simple module/function structure
   - Emit GTKWave `.gtkw` or Surfer `.surfer` save files
4. Add first-divergence report for formal/random failures:
   - Cycle, PC, instruction, register diff, memory diff, CSR diff
   - Simple source span + VHDL signal path + waveform link

**Exit criteria:** VHDL simulation failure can be mapped to Simple source. Waveform groups follow Simple module structure.

**Dependencies:** Phase 1 Agent A (HWIR types for node IDs).

---

## Phase 4 — Advanced (M5–M7)

### Agent C (continued): RV32IMC Performance

- Add M/C extension support to RV32 core
- Pipeline variants for performance
- CoreMark + Dhrystone harness
- QoR comparison against VexRiscv, Ibex

### Agent D (continued): RV64 Application-Class

- Privilege modes, interrupt controller
- Caches (I-cache, D-cache)
- MMU (Sv39 — existing `mmu_sv39.spl`)
- Linux boot path evaluation
- Compare against CVA6/VexiiRiscv class

### Autotune Agent (new):
- QoR feedback file: `.simple/qor/design.target.qor`
- Grid search over FSM encoding, pipeline cuts, resource sharing
- Bayesian optimization for multi-objective Pareto

---

## Execution Rules

1. **File scope is exclusive.** Two agents must never edit the same file in the same phase.
2. **New directories preferred.** When creating new subsystems (HWIR, QoR), use new directories to avoid conflicts.
3. **Commit per deliverable.** Each agent commits after each testable deliverable, not at phase end.
4. **Verify before claiming.** Every VHDL change must pass `ghdl -a` at minimum. No silent normalization of failures.
5. **Evidence over claims.** PPA numbers come from synthesis tools, not estimates. Benchmark results come from simulation, not projections.
6. **Existing tests must not break.** Run `bin/simple test` for touched compiler/lib paths.
7. **No over-engineering.** Each phase delivers the minimum needed for its exit criteria. Autotuning and multi-objective Pareto are Phase 4, not Phase 1.

---

## Recommended Implementation Order

```
Phase 1 (parallel): A(HWIR) + B(VHDL harden) + E(CI) + D(RV64 pipeline)
Phase 2 (after A):   A(HWIR optimizer)
Phase 3 (after E):   C(RV32 QoR) + F(QoR database) + G(debuggability)
Phase 4 (after C+D): RV32IMC perf + RV64 app-class + autotune
```
