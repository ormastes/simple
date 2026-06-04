# Simple RTL Backend Optimization and Production VHDL Generation

- **Status:** Proposal
- **Target:** https://github.com/ormastes/simple
- **Version:** 2.0 (MDSOC+ enriched, local-matched)
- **Date:** 2026-06-01

---

## 1. Goal

Improve the Simple RTL backend to generate production-quality VHDL with competitive performance, area/size, debuggability, and verification quality.

**Core Design Decision:** Do not optimize only the VHDL emitter. Simple should optimize hardware intent before VHDL generation using a hardware-aware IR. The VHDL backend should be a conservative, deterministic, synthesis-friendly serialization stage.

### Competitive Metrics

**Performance:** Fmax, CoreMark/MHz, Dhrystone DMIPS/MHz, CPI, branch/load-use penalty

**Size/Area:** LUT, FF, BRAM, DSP, kGE, cell area, CoreMark/MHz per kGE, CoreMark/s per LUT

---

## 2. Current Local State

### 2.1 Existing VHDL Backend (Layer 70)

The VHDL backend is already substantial with ~35 source files:

| Component | Source | Status |
|-----------|--------|--------|
| VhdlBackend core | `src/compiler/70.backend/backend/vhdl_backend.spl` | Implemented |
| VhdlBuilder (code gen engine) | `src/compiler/70.backend/backend/vhdl/vhdl_builder.spl` | Implemented — `VhdlBuilder` class with entity, port, signal, architecture emit |
| Entity compilation | `src/compiler/70.backend/backend/vhdl_entity_compile.spl` | Implemented — MIR → VHDL entity/architecture via `compile_function()` |
| Expression emission | `src/compiler/70.backend/backend/vhdl_expr.spl` | Implemented |
| Process generation | `src/compiler/70.backend/backend/vhdl_process.spl`, `_part1.spl`, `_part2.spl` | Implemented — combinational + clocked |
| Type mapping | `src/compiler/70.backend/backend/vhdl_type_mapper.spl` | Implemented |
| Validation | `src/compiler/70.backend/backend/vhdl_validation.spl` | Implemented |
| Memory templates | `src/compiler/70.backend/backend/vhdl/vhdl_memory_templates.spl` | Implemented — ROM, RAM, read-during-write policy |
| Clock/reset | `src/compiler/70.backend/backend/vhdl/vhdl_clock_ports.spl` | Implemented — `ClockDomain` class with sync/async reset, `PortBundle` |
| Register file | `src/compiler/70.backend/backend/vhdl/vhdl_register_file.spl` | Implemented |
| RV32I decode | `src/compiler/70.backend/backend/vhdl/vhdl_rv32i_decode.spl` | Implemented |
| Hardware metadata | `src/compiler/70.backend/backend/vhdl/vhdl_hardware_metadata.spl` | Implemented — `HardwareAttr`, `ReturnLabel`, `HardwareCallInstance`, `PortMapEntry` |
| Call lowering | `src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl` | Implemented |
| Bit semantics | `src/compiler/70.backend/backend/vhdl/vhdl_bit_semantics.spl` | Implemented |
| Hardware spawn | `src/compiler/70.backend/backend/vhdl/vhdl_hardware_spawn_lower.spl` | Implemented |
| Subprogram model | `src/compiler/70.backend/backend/vhdl/vhdl_subprogram_model.spl` | Implemented |
| Testbench | `src/compiler/70.backend/backend/vhdl/vhdl_testbench*.spl` (5 files) | Implemented |
| ABI | `src/compiler/70.backend/backend/vhdl/vhdl_abi.spl` | Implemented |
| VHDL constraints | `src/compiler/70.backend/vhdl_constraints.spl` | Implemented |

### 2.2 Driver Integration (Layer 80)

VHDL compilation is wired through the driver layer:
- `src/compiler/80.driver/driver_compile_vhdl_codegen.spl`
- `src/compiler/80.driver/driver_compile_vhdl_expr.spl`
- `src/compiler/80.driver/driver_compile_vhdl_lowering.spl`
- `src/compiler/80.driver/driver_compile_vhdl_source_map.spl`
- `src/compiler/80.driver/driver_compile_vhdl_util.spl`

### 2.3 Existing RV32I RTL Core (Pure Simple)

A complete single-cycle RV32I core exists at `src/lib/hardware/rv32i_rtl/`:

| Module | File | Description |
|--------|------|-------------|
| Core | `core.spl` | Top-level single-cycle datapath: `core_combinational()`, `core_update()`, `core_reset()` |
| ALU | `alu.spl` | `alu_compute()` with signed comparison helpers |
| Decode | `decode.spl` | `decode_instruction()` → `DecodeResult` |
| RegFile | `regfile.spl` | `regfile_create()`, `regfile_read()`, `regfile_write()` |
| LSU | `lsu.spl` | `lsu_load()` for load data alignment |
| CSR | `csr.spl`, `csr_s.spl` | CSR read/write, machine-mode registers |
| Trap | `trap.spl` | Exception/interrupt entry/exit |
| MMU | `mmu_sv32.spl` | Sv32 page table walk |
| Package | `pkg.spl` | Opcodes, funct codes, constants |

**Architecture:** Semihosting-aware (detects `slli zero,zero,0x1f / ebreak / srai zero,zero,0x7` magic sequence).

### 2.4 RV64GC RTL Core

At `src/lib/hardware/rv64gc_rtl/`:
- `core.spl`, `decode.spl`, `alu.spl`, `regfile.spl`
- `mul_div.spl` — M extension
- `atomics.spl` — A extension
- `csr.spl`, `csr_s.spl`, `trap.spl`
- `lsu.spl`, `mmu_sv39.spl` — Sv39 virtual memory
- `pkg.spl`

### 2.5 RV64 Pipelined Core (5-stage)

At `src/lib/nogc_sync_mut/hardware/rv64/pipeline/`:
- `types.spl` — `AluOp` enum (20 operations), `InstrType` enum, `RegFile` struct (32×64-bit)
- `if_stage.spl` — Instruction Fetch
- `id_stage.spl` — Instruction Decode
- `ex_stage.spl` — Execute
- `mem_stage.spl` — Memory
- `wb_stage.spl` — Write-back
- `decoder.spl` — Pipeline decoder

### 2.6 SoC RTL

At `src/lib/hardware/soc_rtl/`:
- `soc_top.spl` — Full RV32I SoC: core + CSR + trap + regfile + Wishbone + RAM + ROM + UART 16550 + CLINT + mailbox
- `soc_top_64.spl` — RV64 variant
- `wb_interconnect.spl`, `wb64_interconnect.spl` — Wishbone bus
- `bootrom.spl`, `ram.spl`, `ram64.spl` — Memory
- `uart16550.spl`, `clint.spl`, `plic.spl`, `mailbox.spl` — Peripherals
- `eth_dma_bridge.spl` — Ethernet DMA

### 2.7 FPGA Linux Integration

At `src/lib/hardware/fpga_linux/`:
- `riscv_fpga_linux.spl` — FPGA + Linux bring-up
- `soc_vhdl_gen.spl`, `soc_vhdl_gen_part1.spl`, `soc_vhdl_gen_part2.spl` — SoC VHDL generation

### 2.8 GHDL Simulation Runners

At `src/lib/nogc_async_mut_noalloc/baremetal/`:
- `ghdl_generated_rv32_runner.shs` — GHDL analysis/elaboration/run for RV32
- `ghdl_generated_rv64_runner.shs` — RV64 variant
- Plus variants: `_boot_info_real_dtb`, `_linux_handoff`, `_mailbox`, `_semihost`, `_strobe`, `_fw_jump`, `_irq`

### 2.9 RTL Debuggability Lint (Layer 35)

`src/compiler/35.semantics/lint/riscv_rtl_debuggability_lint.spl`:
- Lint warnings: `RTLDBG001` (missing debug sidecar), `RTLDBG002` (source-map mismatch), `RTLDBG003` (bundle manifest)
- Checks: proof-lane header, sidecar JSON alignment, debug outputs, observability keys (fetch, trap, halt, memory, registers, probes, proof failure)
- Works with `GeneratedCoreShellContract` from `hardware.riscv_common.pkg`

### 2.10 Existing Hardware Metadata

`VhdlBuilder` generates VHDL-2008 with:
- `library ieee; use ieee.std_logic_1164.all; use ieee.numeric_std.all;`
- Entity/architecture pairs with `"rtl"` architecture name
- `ClockDomain`: `default_domain()` (100 MHz, sync reset), `no_reset()`, `async_reset()`
- Memory templates: ROM, registered ROM, single-port sync RAM with explicit `ReadDuringWritePolicy`
- Diagnostics: `VHDL-MEM-UNCONSTRAINED`, `VHDL-MEM-GENERAL`

### 2.11 HWIR Status

**Not yet implemented.** No `hwir` directory or module exists in the compiler. Currently, MIR is lowered directly to VHDL text via `VhdlBackend.compile_function()`. This is the primary gap this roadmap addresses.

### 2.12 Existing Documentation

| Document | Path |
|----------|------|
| FPGA RTL guide | `doc/07_guide/hardware/simple_generated_fpga_rtl.md` |
| SFFI VHDL guide | `doc/07_guide/hardware/sffi_vhdl_guide.md` |
| Xilinx FPGA bringup | `doc/07_guide/hardware/xilinx_fpga_board_bringup.md` |
| K26 NaxRiscv | `doc/07_guide/hardware/k26_naxriscv_rv64_product.md` |
| KV260 boot | `doc/07_guide/hardware/kv260_rv64gc_fpga_boot.md` |
| Kria K26 bringup | `doc/07_guide/hardware/kria_k26_fpga_bringup.md` |
| RISC-V FPGA Linux design | `doc/05_design/riscv_fpga_linux.md` |
| Generated core migration | `doc/05_design/riscv_generated_core_migration.md` |
| RTL MDSOC capsules | `doc/05_design/rtl_riscv_mdsoc_capsules.md` |
| RV64 pipeline | `doc/05_design/rv64_linux_rtl_pipeline.md` |
| VHDL/Python parity | `doc/05_design/vhdl_python_hdl_parity.md` |
| FPGA inventory | `doc/08_tracking/hardware/riscv64_fpga_inventory_2026-05-19.md` |
| RISC-V guide | `doc/07_guide/riscv_guide.md` |

---

## 3. Proposed RTL Compilation Pipeline

### 3.1 Current Path (direct MIR → VHDL)

```
Simple source → HIR → MIR → VhdlBackend.compile_function() → VHDL text → GHDL
```

### 3.2 Target Path (with HWIR)

```
Simple source
  → typed HIR / MIR
  → hardware legality checker
  → HWIR / RTL-SSA
  → area/speed/resource optimizer
  → scheduled RTL graph
  → VHDL-2008 emitter
  → GHDL simulation
  → ghdl-yosys / Yosys synthesis
  → FPGA / ASIC flow
  → QoR feedback database
```

### 3.3 MDSOC+ Mapping

| Component | MDSOC Layer | Pattern |
|-----------|-------------|---------|
| HWIR types | Layer 50 (shared MIR-adjacent) | Pure data types, no mutation |
| Legality checker | Layer 35 (Semantics) | Lint extension |
| HWIR optimizer | Layer 60 (MIR Opt) | Optimization plugin contract |
| VHDL emitter | Layer 70 (Backend) | Backend capsule |
| Driver integration | Layer 80 (Driver) | Pipeline orchestration |
| QoR database | Userland service | MDSOC outer + ECS inner (per MDSOC+ rules) |

---

## 4. Feature 1 — HWIR and RTL-SSA Optimizer

### 4.1 Proposed HWIR Concepts

```
HwModule         — top-level synthesizable unit
HwPort           — input/output/inout with width, direction, clock domain
HwSignal         — internal wire or register
HwRegister       — clocked storage with reset policy
HwCombOp         — combinational operation node
HwMemory         — inferred memory (block/distributed/register/ROM/FIFO)
HwFsm            — finite state machine with encoding policy
HwPipeline       — pipeline stage with latency/II/valid-ready
HwClockDomain    — clock domain with frequency, reset kind
HwResetPolicy    — sync/async, active-high/low
HwResourceBinding — DSP/LUT/iterative/shared binding
HwSourceMap      — Simple source → HWIR → VHDL mapping
HwCostModel      — area/speed/power estimates per target
```

### 4.2 Optimization Passes

| Pass | Description | Existing Analog |
|------|-------------|-----------------|
| Bit-width narrowing | Infer exact ranges, narrow operators/registers/muxes | MIR strength reduction pattern |
| Constant/structural simplification | Constant fold, dead signal/register elimination | `optimization_passes_part1.spl` |
| Area/speed resource binding | Share/duplicate resources based on profile | Target opt planner pattern |
| Pipeline scheduling | Latency-aware, manual/automatic cuts, valid/ready | RV64 pipeline stages |
| FSM optimization | Detect FSMs, choose encoding, verify reset | Existing `ClockDomain` reset policy |
| Memory inference | Register file, block/distributed RAM, ROM, FIFO | `vhdl_memory_templates.spl` patterns |
| DSP inference | mul, MAC, dot product, FIR | Backend optimization passes |
| Retiming metadata | Source-map preservation, debug attribute control | `driver_compile_vhdl_source_map.spl` |

### 4.3 RTL Profiles

```
@rtl_profile("area")      — share multipliers, iterative divide, binary FSM
@rtl_profile("speed")     — pipeline, DSP blocks, one-hot FSM, reduce mux depth
@rtl_profile("balanced")  — target cost model chooses
```

### 4.4 CLI

```bash
simple compile --backend=vhdl --rtl-profile=area
simple compile --backend=vhdl --rtl-profile=speed
simple compile --backend=vhdl --rtl-profile=balanced
simple compile --backend=vhdl --rtl-report=ppa
simple compile --backend=vhdl --rtl-explain=all
```

---

## 5. Feature 2 — Production VHDL Hardening

### 5.1 Target Profiles

| Profile | Controls |
|---------|----------|
| `generic-vhdl-2008` | Portable VHDL-2008, no vendor attributes |
| `ghdl-yosys` | GHDL analysis + ghdl-yosys synthesis |
| `vivado` | Xilinx attributes, BRAM/DSP inference pragmas |
| `quartus` | Intel/Altera attributes |
| `yosys-nextpnr` | Open-source FPGA (iCE40, ECP5) |
| `openroad-asic` | ASIC-style: Liberty, LEF/DEF, standard cells |

### 5.2 Existing Strengths

Already implemented:
- `ieee.numeric_std` usage (via `VhdlBuilder.emit_library_header()`)
- Explicit clock/reset policy (`ClockDomain` class with sync/async)
- Memory template library (ROM, registered ROM, sync RAM with read-during-write policy)
- Type-safe signal declarations (MIR type → VHDL type mapping)
- Diagnostic codes (`VHDL-MEM-UNCONSTRAINED`, `VHDL-MEM-GENERAL`)
- Source-map generation (`driver_compile_vhdl_source_map.spl`)

### 5.3 Gaps to Fill

- Vendor-specific attribute emission (conditional on target profile)
- DSP inference templates
- CDC primitives (`@cdc_sync`, `@async_fifo`, `@gray_counter`)
- Black-box / vendor IP boundary support
- GHDL CI lanes (analysis → elaboration → simulation → synthesis)
- Deterministic naming for release builds

---

## 6. Feature 3 — RISC-V Core Proof Targets

### 6.1 Existing Cores (Current State)

| Core | Source | Architecture | Status |
|------|--------|--------------|--------|
| RV32I single-cycle | `src/lib/hardware/rv32i_rtl/` | Single-cycle, Wishbone | Implemented + GHDL runners |
| RV64GC | `src/lib/hardware/rv64gc_rtl/` | Multi-cycle/pipelined | Implemented |
| RV64 5-stage pipeline | `src/lib/nogc_sync_mut/hardware/rv64/pipeline/` | IF/ID/EX/MEM/WB | Implemented |
| RV32I SoC | `src/lib/hardware/soc_rtl/soc_top.spl` | Core + peripherals | Implemented |
| RV64 SoC | `src/lib/hardware/soc_rtl/soc_top_64.spl` | 64-bit variant | Implemented |

### 6.2 Reference Competitors

| Core | Role |
|------|------|
| SERV | Smallest-area RV32 reference |
| PicoRV32 | Tiny FPGA RV32 baseline |
| NEORV32 | Strong VHDL-style RV32 baseline |
| VexRiscv | Configurable high-quality RV32 FPGA baseline |
| Ibex | Production-quality RV32 verification/ASIC baseline |
| VexiiRiscv | High-performance RV32/RV64 stretch target |
| CVA6 | RV64 Linux-capable application-class reference |

### 6.3 Target Stages

**Stage A — RV32 Area:** `simple-rv32e-area`, `simple-rv32i-tiny`, `simple-rv32im-compact`
- Baseline: existing `rv32i_rtl/` core
- Gate: LUT ≤ 1.5× PicoRV32 small, formal pass (RVFI)

**Stage B — RV32 Performance:** `simple-rv32imc-balanced`, `simple-rv32imc-fast`
- Baseline: existing pipeline work
- Gate: CoreMark/MHz within 25% of VexRiscv small productive

**Stage C — RV64 Functional:** `simple-rv64i-min`, `simple-rv64im-embedded`
- Baseline: existing `rv64gc_rtl/` + `rv64/pipeline/`
- Gate: RV64I formal pass, ISA tests pass

**Stage D — RV64 Application-Class:** `simple-rv64gc-linux`
- Baseline: existing SoC + MMU (Sv39)
- Gate: compare against CVA6/VexiiRiscv class

---

## 7. Feature 4 — QoR Database and Benchmark Harness

### 7.1 QoR Schema (MDSOC+ ECS)

```
entity RtlQorRun:
    commit_hash: text
    compiler_version: text
    target_profile: text
    synthesis_tool: text
    device_or_pdk: text
    design_name: text
    source_hash: text
    hwir_hash: text
    vhdl_hash: text
    test_status: text
    formal_status: text
    fmax_mhz: f64
    lut_count: i64
    ff_count: i64
    bram_count: i64
    dsp_count: i64
    kge: f64
    coremark_per_mhz: f64
    dmips_per_mhz: f64
```

### 7.2 Commands

```bash
simple rtl bench --suite=smoke
simple rtl bench --suite=riscv32
simple rtl bench --suite=riscv64
simple rtl ppa --target=ice40|ecp5|artix7|sky130
simple rtl compare --against=picorv32,vexriscv,ibex,neorv32
simple rtl qor report --format=html
```

### 7.3 CI Regression Policy

- Correctness regression: **fail always**
- Synthesis regression: **fail always**
- VHDL nondeterminism: **fail always**
- Area regression > 5%: warn → fail on protected benchmarks
- Fmax regression > 5%: warn → fail on protected benchmarks

---

## 8. Feature 5 — Verification (RVFI, Formal, Co-Simulation)

### 8.1 RVFI Interface Signals

Standard signals: `rvfi_valid`, `rvfi_order`, `rvfi_insn`, `rvfi_trap`, `rvfi_rs1_addr/rdata`, `rvfi_rs2_addr/rdata`, `rvfi_rd_addr/wdata`, `rvfi_pc_rdata/wdata`, `rvfi_mem_addr/rmask/wmask/rdata/wdata`

### 8.2 Commands

```bash
simple rtl verify --core=simple-rv32i-tiny --formal=rv32i
simple rtl verify --riscv-dv --isa=rv32imc
simple rtl verify --co-sim --iss=spike
```

### 8.3 Coverage Targets

Instruction, CSR, exception, branch/jump, load/store alignment, pipeline hazard, reset, interrupt, debug-mode coverage.

---

## 9. Feature 6 — RTL Debuggability

### 9.1 Existing Infrastructure

- Source-map generation: `driver_compile_vhdl_source_map.spl`
- Debug sidecar: `.debug.json` with `sourceMap`, `debugOutputs`, `observability`
- Lint enforcement: `riscv_rtl_debuggability_lint.spl` (RTLDBG001–003, RTLDBG101)
- Bundle manifest: `riscv_fpga_rtl_manifest.sdn`

### 9.2 Source Map Format

```
SimpleRtlSourceMap:
    simple_file, simple_line, simple_column
    hwir_node_id
    vhdl_file, vhdl_line, vhdl_signal
    clock_domain, reset_domain, resource_binding
```

### 9.3 Commands

```bash
simple rtl sim --wave=out.fst
simple rtl wave out.fst --source-map=out.srmap
simple rtl trace --signal alu.result
simple rtl explain --vhdl-line generated/core.vhd:244
```

---

## 10. Feature 7 — RTL Support Matrix (Executable)

### 10.1 Categories

Integer widths, arithmetic, control, combinational logic, clocked logic, memory, arrays/structs/enums, pipelines, CDC, black boxes, debug, synthesis, negative tests (unsupported float, pointer, dynamic allocation, unbounded loop, multiple drivers).

### 10.2 Commands

```bash
simple rtl test --matrix
simple rtl test --negative
simple rtl test --synthesis
simple rtl test --formal
simple rtl test --all
```

---

## 11. Feature 8 — QoR Feedback and Autotuning

### 11.1 Autotunable Choices

FSM encoding, pipeline cut placement, resource sharing, DSP vs LUT multiplier, RAM kind, register balancing, branch predictor size, cache size, debug signal preservation.

### 11.2 Commands

```bash
simple rtl autotune core.spl --target=artix7 --objective=area
simple rtl autotune core.spl --target=artix7 --objective=speed
simple rtl autotune core.spl --target=sky130 --objective=coremark_per_kge
```

---

## 12. Milestones

| Milestone | Description | Existing Foundation | Exit Criteria |
|-----------|-------------|---------------------|---------------|
| M0 | Baseline Audit | GHDL runners exist, `rv32i_rtl` core exists | `simple rtl test --matrix` passes, first QoR report |
| M1 | HWIR + Legality Checker | MIR types at Layer 50, validation at `vhdl_validation.spl` | MIR → HWIR → VHDL matches current behavior |
| M2 | Area/Speed Optimizer | MIR opt passes (Layer 60), memory templates | Area mode reduces LUT, speed mode improves Fmax |
| M3 | Toolchain Hardening | GHDL runners, driver VHDL files | CI lanes: analysis → elaboration → sim → synthesis |
| M4 | RV32I Tiny Core QoR | `rv32i_rtl/core.spl` + SoC | Formal pass, ISA tests, PPA report vs PicoRV32 |
| M5 | RV32IMC Performance | Pipeline work in progress | CoreMark/MHz vs VexRiscv/Ibex |
| M6 | RV64I/RV64IMAC | `rv64gc_rtl/`, `rv64/pipeline/` | RV64I formal, synthesis report |
| M7 | RV64 Application-Class | SoC + Sv39 MMU | Compare against CVA6 |

---

## 13. Related Documents

- `doc/07_guide/hardware/simple_generated_fpga_rtl.md`
- `doc/07_guide/hardware/sffi_vhdl_guide.md`
- `doc/05_design/riscv_fpga_linux.md`
- `doc/05_design/rtl_riscv_mdsoc_capsules.md`
- `doc/05_design/rv64_linux_rtl_pipeline.md`
- `doc/05_design/riscv_generated_core_migration.md`
- `doc/05_design/vhdl_python_hdl_parity.md`
- `doc/03_plan/agent_tasks/vhdl_mir_backend_abi.md`
- `doc/03_plan/agent_tasks/pure_simple_vhdl_riscv_gap_spawn_plan.md`
- `doc/03_plan/agent_tasks/vhdl_subprogram_emission.md`
- `doc/03_plan/agent_tasks/vhdl_testbench_conversion.md`
- `doc/03_plan/agent_tasks/riscv_fpga_linux_rtl_completion.md`
- `doc/08_tracking/hardware/riscv64_fpga_inventory_2026-05-19.md`
