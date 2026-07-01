# RTL Simulation & Fast-Mode Functional Simulation for RISC-V 32

**Research Date:** 2026-03-27
**Scope:** Open-source RTL simulators, RISC-V functional simulators, hybrid approaches, timing models, and RV32 cores

---

## 1. Open-Source RTL Simulators

### 1.1 Verilator

- **What:** Compiles Verilog/SystemVerilog into cycle-accurate C++ or SystemC models. Not a traditional event-driven simulator — it is a *compiler* that generates optimized multithreaded C++ code.
- **License:** LGPL 3.0 or Artistic 2.0
- **Simulation Type:** Cycle-based, 2-state (no X/Z propagation in most contexts). Removes all notions of time/delays; simulates clock-edge to clock-edge.
- **Performance:** The fastest open-source RTL simulator. Routinely beats commercial event-driven simulators. Chipyard documents Verilator-based RTL simulation at **O(1 KHz)** for full SoC designs (e.g., Rocket chip). For simpler designs, speeds can be much higher. Can be **500x faster than Icarus Verilog**. Supports multithreaded simulation for additional speedup.
- **Cosimulation Interfaces:**
  - **DPI-C** (SystemVerilog Direct Programming Interface): Import/export C functions callable from SV and vice versa. This is the primary high-performance interface.
  - **VPI** (Verilog Procedural Interface): Supported but limited subset — inspection, value change callbacks, depositing values to public signals. VPI is inherently slower than direct C++ access (hundreds of instructions per access vs. a couple for direct references).
  - **SystemC:** Can output SystemC-compatible models, enabling integration with TLM-based environments.
  - **Direct C++ API:** Generated model exposes top-level IO as C++ references. Fastest integration path.
- **Integration with Custom Fast Simulator:** Excellent. The generated C++ model can be linked directly into any C++ program. A fast functional simulator can call `eval()` on each clock cycle, inject/read signals via direct C++ references, and use DPI-C for more structured interaction. This is the most common approach in the RISC-V ecosystem (used by Chipyard, Ibex, CVA6, etc.).
- **Limitations:** No SDF back-annotation, no mixed-signal, limited X/Z handling. Synthesizable RTL only (with exceptions for some verification constructs). No intra-cycle timing.

### 1.2 CXXRTL (Yosys Backend)

- **What:** A simulation backend in Yosys that compiles designs into C++ code, similar in concept to Verilator but integrated into the Yosys synthesis framework.
- **License:** ISC (Yosys license)
- **Simulation Type:** Cycle-based. Single-pass evaluation model. Uses C++ templates for bit-vector data representation.
- **Performance:** Approximately **8x slower than single-threaded Verilator** on a VexRiscv benchmark (per Tom Verbeure's evaluation). Only generates a single C++ file (no parallel compilation). Template-heavy code causes slow C++ compilation times.
- **Key Features:**
  - **Black-box support:** Any module can be replaced with a behavioral C++ model. Supports parameterized modules via C++ templates. This is extremely valuable — you can replace a CPU core with a fast functional model, a UART with a host serial bridge, or a JTAG controller with a GDB bridge.
  - **Design introspection:** Runtime discovery of all signals and memories — useful for building custom debuggers and monitors.
  - **VCD waveform generation:** Built-in, simple implementation (~200 lines).
  - **Implementation simplicity:** The entire CXXRTL backend is compact and understandable.
- **Integration with Custom Fast Simulator:** Strong, primarily through the black-box mechanism. You can replace any submodule (e.g., a CPU core) with a C++ behavioral model that runs your fast simulator. The black-boxing with template parameters makes this especially flexible.
- **Limitations:** Slower than Verilator, single-threaded only, no SystemVerilog support (only what Yosys can parse), single-file output hurts compilation parallelism.

### 1.3 Icarus Verilog

- **What:** Traditional event-driven Verilog simulator. Compiles Verilog to an intermediate form (VVP) which is then interpreted.
- **License:** GPL 2.0
- **Simulation Type:** Event-driven, 4-state (full X/Z support). Supports behavioral constructs: delays, `repeat`, `initial`, `always`, etc.
- **Performance:** Very slow — roughly **500x slower than Verilator**. Adequate for small designs and quick functional checks.
- **Cosimulation Interfaces:** Full VPI support (the standard Verilog PLI/VPI interface). Can load VPI modules as shared libraries. Cocotb uses Icarus via VPI.
- **Integration with Custom Fast Simulator:** Through VPI callbacks. A C shared library implementing VPI can interface with Icarus, but the slowness of the simulator makes this impractical for any serious workload.
- **Best Use:** Quick testbench development, designs requiring full behavioral Verilog support, educational purposes.

### 1.4 GHDL

- **What:** Open-source VHDL simulator supporting VHDL-87, VHDL-93, and VHDL-2008. Can use LLVM, GCC, or mcode as backend for code generation.
- **License:** GPL 2.0
- **Simulation Type:** Event-driven. Full VHDL behavioral support.
- **Performance:** Faster than Icarus for VHDL designs; the LLVM/GCC backends compile to native code. Still event-driven, so slower than cycle-based approaches.
- **Cosimulation Interfaces:** VHPI (VHDL Procedural Interface), Cocotb support via GPI layer, VCD/GHW waveform output.
- **Integration:** Relevant only if your RTL is in VHDL. Can work with Cocotb for Python-driven testbenches. pyGHDL provides Python bindings to the GHDL AST.
- **Relevance for RV32:** Most open-source RISC-V cores are in Verilog/SystemVerilog. GHDL is relevant only for VHDL-based cores or mixed-language simulation (GHDL + Yosys plugin for synthesis).

### 1.5 Cocotb

- **What:** Python-based coroutine cosimulation testbench framework. Not a simulator itself — it drives any supported RTL simulator via standard interfaces.
- **License:** BSD 3-Clause
- **How it works:** Uses a GPI (Generic Procedural Interface) abstraction layer that maps to VPI (Verilog), VHPI (VHDL), or FLI. The DUT runs in the RTL simulator; Python coroutines drive stimulus and check outputs. `await` yields control back to the simulator to advance time.
- **Supported simulators:** Verilator, Icarus Verilog, GHDL, Synopsys VCS, Cadence Xcelium, Mentor Questa/ModelSim, Aldec Riviera-PRO, and others.
- **Performance:** Limited by the simulator backend and the Python-RTL boundary overhead. Best for verification, not for high-speed simulation.
- **Integration with Custom Fast Simulator:** Cocotb could serve as the testbench orchestration layer, driving both an RTL simulator and a fast functional model. The Python layer would coordinate the two, comparing outputs. However, the Python overhead makes this unsuitable for tight-loop cosimulation.

### 1.6 Other Notable Open-Source Simulators

| Simulator | Notes |
|-----------|-------|
| **nvc** | Open-source VHDL simulator (event-driven, LLVM JIT). Growing community. |
| **Amaranth (nMigen)** | Python HDL framework; uses Yosys+CXXRTL for simulation. |
| **Chisel/FIRRTL** | Scala-based HDL; generates Verilog for Verilator simulation (used by Chipyard/Rocket). |
| **SpinalHDL** | Scala-based HDL (VexRiscv is written in it); generates Verilog for Verilator. Has SpinalSim for integrated simulation. |

---

## 2. Fast Functional Simulators for RISC-V 32

### 2.1 Spike (riscv-isa-sim)

- **What:** The official RISC-V ISA reference simulator. Implements a functional model of one or more RISC-V harts. Named after the golden spike of the US transcontinental railway.
- **License:** BSD 3-Clause
- **ISA Support:** Comprehensive — RV32I/RV64I, RV32E/RV64E, M, A, F, D, Q, C, B, V, P extensions, Zk* crypto, hypervisor, all privilege modes (M/S/U), Sv32/Sv39/Sv48/Sv57 virtual memory.
- **Performance:** Interpretive execution — typically **10-50 MIPS** on modern hardware. Sequential, instruction-at-a-time. No dynamic binary translation.
- **Cosimulation:** Spike is widely used as the golden reference model for tandem verification. It can generate commit logs (instruction trace with register updates) that RTL can be compared against. Dromajo was specifically designed to provide a similar commit-log API.
- **Integration:** Can be compiled as a library (`libriscv`) and called from C++. Custom devices and extensions can be added via plugins. The commit-log interface enables instruction-by-instruction comparison with RTL.
- **RTL Boundary:** Instruction-level. At each retired instruction, Spike produces (PC, instruction, register writeback, memory access) tuples that can be compared with RTL trace output. No cycle-level accuracy.

### 2.2 QEMU

- **What:** Full-system emulator using TCG (Tiny Code Generator) dynamic binary translation. Supports `qemu-system-riscv32` and `qemu-system-riscv64`.
- **License:** GPL 2.0
- **Performance:** **100-1000 MIPS** depending on workload. DBT translates guest basic blocks to host machine code at runtime. Orders of magnitude faster than interpretive simulators.
- **Machine Support:** Multiple board models including `virt` (generic virtual platform suitable for Linux), `sifive_e`, `sifive_u`, `spike`, `microchip-icicle-kit`, and others.
- **Cosimulation:** QEMU is not typically used for RTL cosimulation because:
  - No cycle-level accuracy whatsoever
  - Basic blocks are translated and cached, making instruction-level tracing expensive
  - TCG optimizations reorder/combine operations
  - However, QEMU plugins can trace every instruction for offline comparison
- **Integration with Custom Simulator:** QEMU's TCG could theoretically be replaced or augmented, but the architecture is complex. More practically, QEMU serves as a fast boot/checkpoint generator — run workload in QEMU, create a memory checkpoint, then resume in RTL simulation (similar to Dromajo's approach).
- **Best Use:** Fast software development, OS boot testing, workload characterization. Not for hardware verification.

### 2.3 Dromajo

- **What:** RISC-V RV64GC emulator specifically designed for RTL cosimulation. Originally from Esperanto Technology, now under CHIPS Alliance.
- **License:** Apache 2.0
- **Architecture:** Based on Fabrice Bellard's RISCVEMU/TinyEMU, extensively verified and enhanced to ISA 2.3/priv 1.11.
- **Key Innovation: Checkpoint + Cosimulation Workflow:**
  1. Run application (e.g., Linux + benchmark) under fast software simulation
  2. Generate checkpoint after N cycles (captures full architectural state + memory image)
  3. Resume checkpoint in RTL cosimulation for detailed HW/SW co-verification
  - This decouples the slow boot/initialization phase from the interesting verification window
- **Cosimulation API:** Simple C API designed to be called from RTL testbench (Verilator or VCS). At each committed instruction, the RTL calls Dromajo to step the reference model and compare results.
- **Performance:** Fast for software execution (interpretive, similar to Spike). The cosimulation mode adds overhead due to per-instruction comparison.
- **Integration:** Designed specifically for this purpose. Chipyard integrates Dromajo for tandem verification of BOOM and Rocket cores.
- **Limitation:** Currently RV64GC only. For RV32, modifications would be needed (or use Spike instead).

### 2.4 Sail RISC-V Model

- **What:** The official formal specification of the RISC-V ISA, written in the Sail architecture description language. Maintained by the RISC-V Foundation.
- **License:** BSD 2-Clause
- **What it generates:**
  - **C++ emulator:** Can execute RISC-V ELF files, boot Linux, FreeBSD, and seL4. Supports RV32 and RV64.
  - **OCaml emulator:** Alternative execution target
  - **Theorem prover definitions:** For Isabelle, HOL4, Coq — enabling formal proofs about the ISA
  - **RVFI trace output:** For tandem verification via TestRIG protocol
- **Performance:** The C++ emulator is slower than Spike (Sail focuses on specification clarity, not speed). Typically single-digit MIPS.
- **Tandem Verification:** Supports RVFI (RISC-V Formal Interface) format, enabling direct comparison with hardware implementations. Used with TestRIG for cross-testing against Spike and RVBS (Bluespec).
- **Integration:** Best used as a formal reference oracle rather than a fast simulator. Valuable for proving ISA compliance, not for performance simulation.

### 2.5 riscvOVPsim (Imperas/Synopsys)

- **What:** Imperas RISC-V reference simulator, now part of Synopsys after acquisition. The free version (riscvOVPsim) provides a reference model; the commercial version (ImperasDV) provides full DV integration.
- **License:** Freeware (riscvOVPsim for basic use); commercial (ImperasDV for DV integration)
- **Performance:** Imperas claims **hundreds of MIPS** using their proprietary JIT-based simulation engine. Significantly faster than Spike for large workloads.
- **ImperasDV Features:**
  - Out-of-the-box RTL cosimulation integration
  - Reference model steps in lockstep with RTL
  - Supports asynchronous events (interrupts, debug)
  - Step-and-compare verification methodology
- **Integration:** ImperasDV connects to commercial simulators (VCS, Xcelium, Questa) and Verilator via DPI. It provides a SystemVerilog UVM component that wraps the reference model.
- **Relevance:** The gold standard for commercial RISC-V processor verification, but the free version is limited and the full solution requires expensive licenses.

### 2.6 Other Functional Simulators

| Simulator | Description |
|-----------|-------------|
| **gem5** | Microarchitectural simulator. Supports RISC-V. Cycle-approximate (not cycle-accurate). Used for architecture research. ~1-10 MIPS. |
| **TinyEMU** | Fabrice Bellard's lightweight RISC-V emulator. Basis for Dromajo. Very fast interpretive simulation. |
| **RARS** | RISC-V Assembler and Runtime Simulator. Java-based, educational. |
| **rv32emu** | Lightweight RV32 emulator in C. Good for embedded testing. |

---

## 3. Hybrid RTL + Fast Simulation Approaches

### 3.1 The Core Problem

RTL simulation is cycle-accurate but extremely slow (**O(1 KHz)** for SoC designs). Functional simulation is fast (**O(100 MIPS)** for QEMU) but has no cycle accuracy. The gap is approximately **5-6 orders of magnitude**.

Hybrid approaches try to combine both, using fast simulation for "uninteresting" phases and RTL for "interesting" phases.

### 3.2 Checkpoint-and-Resume (Dromajo Pattern)

**How it works:**
1. Run full workload in fast functional simulator (Dromajo, QEMU, Spike)
2. At interesting points, capture full architectural state (registers, CSRs, memory image, device state)
3. Load checkpoint into RTL simulation, resume execution

**Advantages:** Fast boot (seconds vs. days in RTL), can target specific code regions
**Disadvantages:** State transfer must be complete and accurate; peripheral state is hard to checkpoint; the RTL must be warmup-stable (caches, branch predictors may need warming)
**Used by:** Chipyard + Dromajo, Esperanto, many commercial verification teams

### 3.3 Tandem Verification / Commit-Log Comparison

**How it works:**
1. RTL executes and produces a commit trace (PC, instruction, register writeback, exception info) for each retired instruction
2. A reference model (Spike, Dromajo, Sail, ImperasDV) steps in lockstep, producing the same trace format
3. A checker compares every committed instruction between RTL and reference model

**Advantages:** Finds bugs immediately at the instruction boundary. Handles interrupts and exceptions.
**Disadvantages:** Requires RTL to emit commit trace (extra logic). The reference model must handle the same interrupt/exception injection timing.
**Used by:** Ibex (with Spike), CVA6 (with Spike), BOOM (with Dromajo), commercial cores (with ImperasDV)

### 3.4 Black-Box CPU Replacement (CXXRTL Pattern)

**How it works:**
1. In an SoC simulation, replace the CPU RTL with a fast behavioral C++ model
2. The behavioral model executes instructions functionally but responds to the bus interface as if it were the real CPU
3. The rest of the SoC (peripherals, interconnect, memory controllers) runs in cycle-accurate RTL

**Advantages:** Massive speedup when CPU execution is not the focus. Tests peripheral/SoC integration.
**Disadvantages:** CPU timing is wrong (no pipeline effects, no cache behavior). Cannot verify CPU-peripheral timing interactions.
**Implementation:** CXXRTL's black-box feature is purpose-built for this. Verilator's DPI-C can achieve similar results.

### 3.5 Transaction-Level Modeling (TLM) via SystemC

**How it works:**
- SystemC TLM 2.0 (IEEE 1666-2011) defines abstraction levels:
  - **Untimed (UT):** Pure functional, no timing at all. Fastest.
  - **Loosely Timed (LT):** Approximate timing with temporal decoupling. Processes run ahead by a quantum of simulated time. Fast — used for software development.
  - **Approximately Timed (AT):** Models transaction phases (request, response). Closer to RTL timing but still abstract.
- Verilator can generate SystemC-compatible models, enabling integration with TLM environments
- TLM models are typically **100-1000x faster** than RTL simulation

**Advantages:** Standard interfaces (sockets, generic payloads), interoperability, multiple timing fidelity levels
**Disadvantages:** Creating accurate TLM models requires manual effort. TLM-to-RTL boundary can be complex. SystemC adds a dependency.

### 3.6 FPGA-Accelerated Simulation (FireSim)

**How it works:**
- Compile the RTL design for FPGA (AWS F1 instances or local boards)
- Run at FPGA clock speeds: **O(100 MHz)** — 5-6 orders of magnitude faster than software RTL simulation
- FireSim (from UC Berkeley) provides the infrastructure for Chipyard designs

**Advantages:** Near-real-time execution, cycle-accurate, can boot Linux in seconds
**Disadvantages:** Multi-hour FPGA compilation, limited debug visibility, requires FPGA hardware
**Used by:** Chipyard ecosystem, academic research, SiFive

### 3.7 Cosimulation Interface Mechanisms

| Interface | Standard | Speed | Flexibility | Notes |
|-----------|----------|-------|-------------|-------|
| **Direct C++ API** | Verilator-specific | Fastest | Low-level | Direct signal access via generated structs |
| **DPI-C** | IEEE 1800 (SystemVerilog) | Fast | Good | C function import/export. Supported by Verilator, VCS, Xcelium |
| **VPI** | IEEE 1364 (Verilog) | Slow | Very flexible | Runtime signal lookup. Hundreds of instructions per access. Used by Cocotb |
| **VHPI** | IEEE 1076 (VHDL) | Slow | Very flexible | VHDL equivalent of VPI |
| **Socket-based** | Custom (TCP/IP) | Slowest | Maximum flexibility | Used for cross-process/cross-machine cosimulation. Adds latency. |
| **Shared memory** | Custom | Fast | Good | Memory-mapped regions shared between simulator and external process |

---

## 4. Timing Models

### 4.1 Event-Driven Simulation Timing

- **How it works:** Signal changes create "events" scheduled at future times. Events are processed in time order. A change at time T with delay D creates an event at T+D.
- **Granularity:** Can model intra-cycle behavior, setup/hold times, propagation delays
- **Speed:** Proportional to activity — more signal changes = slower simulation
- **Used by:** Icarus Verilog, GHDL, all commercial event-driven simulators (VCS, Questa, Xcelium)

### 4.2 Cycle-Based Simulation (Verilator, CXXRTL)

- **How it works:** No delays. Every gate/register is evaluated every cycle. Time advances in fixed clock-edge increments.
- **Granularity:** Clock-cycle level only. No intra-cycle timing.
- **Speed:** Constant per cycle regardless of activity. Faster due to optimizations (skip unchanged gates).
- **Timing model:** None. The design is assumed to meet timing. Verification of timing closure is done separately via static timing analysis (STA).

### 4.3 Standard Delay Format (SDF)

- **What:** IEEE 1497 standard. ASCII file format for timing data. Used for back-annotation of gate-level netlists with actual delays from place-and-route.
- **Contents:** Path delays, timing constraint values (setup, hold, recovery, removal), interconnect delays, timing checks
- **Three delay values:** Minimum, typical, maximum (for different process corners)
- **Usage flow:**
  1. Synthesis produces gate-level netlist
  2. Place-and-route computes actual wire delays
  3. SDF file is generated with per-path delays
  4. Event-driven simulator reads SDF and annotates delays onto the netlist
  5. Gate-level simulation with realistic timing catches setup/hold violations
- **Verilator:** Does NOT support SDF annotation (by design — it removes all timing)
- **Icarus Verilog:** Partial SDF support
- **Commercial simulators:** Full SDF support (VCS, Questa, Xcelium)

### 4.4 How Fast Simulators Approximate Timing

| Approach | Timing Accuracy | Speed |
|----------|-----------------|-------|
| **None (Spike, QEMU)** | Instruction count only | Fastest (10-1000 MIPS) |
| **CPI model** | Constant cycles-per-instruction estimate | Fast, ~90% accurate for simple pipelines |
| **Pipeline model (gem5)** | Cycle-approximate with pipeline stages, caches, branch prediction | Slow (1-10 MIPS), ~95% accurate |
| **RTL simulation** | Cycle-accurate | Slowest (1 KHz for SoC) |
| **FPGA emulation** | Cycle-accurate | Fast (100 MHz) but long compile |

For a fast simulator targeting a specific RV32 core, a good middle ground is a **CPI model** — a lookup table of base CPI per instruction class (ALU: 1, load: 2, branch-taken: 3, etc.) with modifiers for cache misses and hazards. This gives reasonable timing estimates at interpretive-simulation speeds.

---

## 5. RISC-V 32 RTL Cores Suitable for Simulation

### 5.1 PicoRV32

- **What:** Size-optimized RV32I[M][A][C] CPU. Single Verilog file (`picorv32.v`).
- **License:** ISC
- **Author:** Claire Wolf (YosysHQ)
- **Architecture:** Non-pipelined, multi-cycle. CPI ~4 average.
- **Performance:** 0.516 DMIPS/MHz (with FAST_MUL, DIV, BARREL_SHIFTER)
- **Size:** Very small — designed for FPGAs with tight area budgets
- **CPI Table:**
  - ALU reg+imm: 3 cycles
  - ALU reg+reg: 3 cycles
  - Branch not taken: 3, taken: 5
  - Load: 5, Store: 5
  - Shift: 4-14 (1 with barrel shifter)
  - MUL: 40, DIV: 40
- **Simulation:** Trivial to simulate with Verilator (single file, simple interface). Has native memory interface and PCPI (Pico Co-Processor Interface) for extensions.
- **Best for:** Simplest possible core for learning, small SoCs, easy Verilator integration. Great starting point for cosimulation experiments.

### 5.2 SERV

- **What:** Award-winning bit-serial RISC-V CPU. World's smallest RISC-V core.
- **License:** ISC
- **Architecture:** Processes one bit per cycle (serial ALU). RV32I[M][C] with Zicsr.
- **Size:** 198 LUT (iCE40), 125 LUT (Artix-7), 2.1 kGE (CMOS)
- **Performance:** Very low — ~32 cycles per ALU bit operation = hundreds of cycles per instruction. Designed for minimum area, not speed.
- **Simulation:** Easy to simulate (small). Uses FuseSoC build system. Verilator support included.
- **Best for:** Extreme area constraints, soft-core packing (many cores in one FPGA), educational. Not practical for performance-oriented simulation experiments.

### 5.3 VexRiscv

- **What:** Highly configurable RISC-V CPU written in SpinalHDL (Scala).
- **License:** MIT
- **Architecture:** Plugin-based, configurable from 2 to 5+ pipeline stages. RV32I[M][A][F[D]][C].
- **Performance:** 1.44 DMIPS/MHz (nearly all features), 1.57 DMIPS/MHz with divider lookup table
- **Key Feature: Plugin Architecture:** Nearly everything is a plugin — PC manager, register file, hazard logic, branch prediction, caches, MMU, FPU. You can compose exactly the CPU you need.
- **Ecosystem:**
  - Linux capable (via LiteX)
  - Zephyr, FreeRTOS support
  - SMP support (VexRiscvSmpCluster)
  - Debug support (JTAG, GDB)
  - Tightly coupled memory support
- **Simulation:** Generates Verilog, then simulated with Verilator. SpinalSim provides integrated simulation from Scala testbenches. The generated Verilog is clean and Verilator-friendly.
- **Best for:** Most flexible option. Ideal for research and custom CPU experiments. The plugin system means you can add/remove features without touching core code.

### 5.4 Ibex (lowRISC)

- **What:** Small 32-bit RISC-V CPU core (RV32I[M][C][B]), previously known as zero-riscy. Part of the OpenTitan project.
- **License:** Apache 2.0
- **Architecture:** 2-stage pipeline (or 3 with writeback stage). Configurable multiplier (1-cycle or 3-cycle).
- **Configurations and Performance:**
  - "micro" (RV32EC): 0.904 CoreMark/MHz, 16.85 kGE
  - "small" (RV32IMC, 3-cycle mult): 2.47 CoreMark/MHz, 26.60 kGE
  - "maxperf" (RV32IMC, 1-cycle mult, branch target ALU, writeback stage): 3.13 CoreMark/MHz, 32.48 kGE
  - "maxperf-pmp-bmfull" (RV32IMCB + PMP): 3.13 CoreMark/MHz, 66.02 kGE
- **Verification:** Extensive DV infrastructure using UVM. Cosimulation with Spike for reference checking. Formal verification support. Verified configurations marked "Green" status.
- **Simulation:** Full Verilator support. Simple System platform for standalone simulation. Includes Yosys synthesis flow for area estimates.
- **Best for:** Production-quality embedded core with thorough verification. Excellent for learning DV methodology. Well-documented, actively maintained.

### 5.5 CVA6 (formerly Ariane)

- **What:** Highly configurable 6-stage in-order RISC-V core. Supports both 32-bit and 64-bit configurations. Application-class (boots Linux). Part of OpenHW Group's CORE-V family.
- **License:** Solderpad Hardware License 0.51 (permissive, similar to Apache 2.0)
- **Architecture:** 6-stage pipeline (PC gen, fetch, decode, issue, execute, commit). RV32/RV64 GC. Branch prediction, instruction/data caches, MMU (Sv32/Sv39), PMP.
- **Performance:** Application-class — boots Linux. ~3-4 CoreMark/MHz (64-bit config).
- **Verification:** UVM-based DV, cosimulation with Spike/Imperas.
- **Simulation:** Verilator support via Chipyard or standalone. Also supports VCS. Has a `perf-model` directory suggesting analytical performance modeling.
- **Best for:** If you need a Linux-capable RV32/RV64 core with full MMU. More complex than Ibex but much more capable. Good for full-system simulation experiments.

---

## 6. Comparative Summary

### Simulation Speed Hierarchy

```
FPGA Emulation (FireSim)     : ~100 MHz        (cycle-accurate)
QEMU (DBT)                   : ~100-1000 MIPS  (no cycle accuracy)
riscvOVPsim (JIT)            : ~100+ MIPS      (no cycle accuracy)
Spike (interpretive)         : ~10-50 MIPS     (instruction-accurate)
Sail C emulator              : ~1-5 MIPS       (instruction-accurate)
gem5 (microarch sim)         : ~1-10 MIPS      (cycle-approximate)
Verilator (cycle sim)        : ~1-100 KHz      (cycle-accurate)
CXXRTL (cycle sim)           : ~0.1-10 KHz     (cycle-accurate)
Icarus Verilog (event sim)   : ~0.01-1 KHz     (event-accurate)
Gate-level + SDF             : ~0.001-0.1 KHz  (timing-accurate)
```

### Decision Matrix: Which Tool for Which Purpose?

| Goal | Best Tool(s) |
|------|-------------|
| Fast software development | QEMU, Spike |
| ISA compliance verification | Spike, Sail, riscvOVPsim |
| RTL functional verification | Verilator + Spike cosimulation |
| SoC integration testing | Verilator + CXXRTL black-boxing |
| Full-system boot testing | QEMU (fast) or FireSim (cycle-accurate) |
| Timing verification | Gate-level sim with SDF (commercial tools) |
| Architecture exploration | gem5 |
| Formal ISA proofs | Sail RISC-V model |
| Custom fast-mode simulation | Verilator (RTL) + Spike/custom interpreter (fast) via DPI-C |

### Recommended Architecture for Custom IR-Based Fast Simulator

For integrating a custom IR-based fast simulator with RTL simulation of an RV32 core:

1. **RTL Core Selection:** Start with **PicoRV32** (simplest) or **Ibex** (production quality with existing DV). VexRiscv for maximum configurability.

2. **RTL Simulator:** **Verilator** — no serious alternative for open-source cycle-accurate simulation.

3. **Cosimulation Approach:** Use the **tandem verification pattern**:
   - RTL (Verilator) emits commit trace via DPI-C
   - Your custom fast simulator maintains shadow architectural state
   - Compare at every committed instruction
   - On mismatch, dump detailed state for debugging

4. **Fast-Mode Switching:** Implement **checkpoint-and-resume** (Dromajo pattern):
   - Boot/initialize in fast simulator
   - Checkpoint architectural state (32 GPRs, PC, CSRs, memory image)
   - Load into Verilator RTL model
   - Run cycle-accurate for region of interest
   - Resume fast simulation after

5. **DPI-C Bridge:** Write a thin DPI-C layer between Verilator and your simulator:
   ```
   // In SystemVerilog wrapper
   import "DPI-C" function void fast_sim_step(input int pc, input int insn, input int rd_val);
   import "DPI-C" function void fast_sim_checkpoint(output int mem[], output int regs[]);
   ```

6. **Performance Target:** With Verilator on a simple RV32 core (PicoRV32), expect **10-100 KHz** RTL simulation speed. Your fast simulator should target **10+ MIPS** for the speed differential to be worthwhile. The checkpoint-resume approach gives the best of both worlds.

---

## 7. Key References

| Resource | URL |
|----------|-----|
| Verilator | https://verilator.org |
| CXXRTL blog (Tom Verbeure) | https://tomverbeure.github.io/2020/08/08/CXXRTL-the-New-Yosys-Simulation-Backend.html |
| Yosys | https://github.com/YosysHQ/yosys |
| Icarus Verilog | https://github.com/steveicarus/iverilog |
| GHDL | https://github.com/ghdl/ghdl |
| Cocotb | https://github.com/cocotb/cocotb |
| Spike | https://github.com/riscv-software-src/riscv-isa-sim |
| QEMU RISC-V | https://www.qemu.org/docs/master/system/target-riscv.html |
| Dromajo | https://github.com/chipsalliance/dromajo |
| Sail RISC-V | https://github.com/riscv/sail-riscv |
| ImperasDV | https://www.synopsys.com/verification/simulation/imperasdv.html |
| PicoRV32 | https://github.com/YosysHQ/picorv32 |
| SERV | https://github.com/olofk/serv |
| VexRiscv | https://github.com/SpinalHDL/VexRiscv |
| Ibex | https://github.com/lowRISC/ibex |
| CVA6 | https://github.com/openhwgroup/cva6 |
| Chipyard | https://chipyard.readthedocs.io |
| FireSim | https://fires.im |
| gem5 RISC-V | https://www.gem5.org |
| IEEE 1497 (SDF) | Standard Delay Format specification |
| IEEE 1666-2011 (SystemC/TLM) | SystemC Language Reference Manual |
