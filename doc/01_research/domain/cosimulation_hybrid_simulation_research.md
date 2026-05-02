# Cosimulation Techniques, Timing Models, and Hybrid Simulation Architectures
## Deep Research Report — 2026-03-27

---

## Table of Contents
1. [Cosimulation Architectures](#1-cosimulation-architectures)
2. [Fast Mode / RTL Mode Switching](#2-fast-mode--rtl-mode-switching)
3. [Timing Models for RISC-V](#3-timing-models-for-risc-v)
4. [Hybrid Simulator Projects](#4-hybrid-simulator-projects)
5. [RTL Concepts for IR Design](#5-rtl-concepts-for-ir-design)
6. [Comprehensive Comparison](#6-comprehensive-comparison)
7. [Recommendations](#7-recommendations)

---

## 1. Cosimulation Architectures

### 1.1 SystemC TLM (Transaction Level Modeling)

**What it is:** SystemC is a set of C++ classes providing an event-driven simulation kernel (IEEE 1666-2011). TLM-2.0 is the standardized transaction-level modeling layer on top of it.

**Abstraction levels:**
- **Untimed (UT):** Pure functional modeling, no timing. Maximum simulation speed.
- **Loosely-Timed (LT):** Uses `b_transport()` (blocking transport). Transactions complete in a single function call with an annotated delay. Temporal decoupling allows each initiator to run ahead of the global simulation time by a configurable quantum, dramatically reducing context switches. Typical speed: **100-1000 MIPS** for SoC-level models.
- **Approximately-Timed (AT):** Uses `nb_transport_fw()`/`nb_transport_bw()` (non-blocking transport) with explicit BEGIN_REQ/END_REQ/BEGIN_RESP/END_RESP phases. Models pipeline effects and contention. Typical speed: **1-10 MIPS**.
- **Cycle-Accurate (CA):** Pin-level or signal-level modeling. Speed comparable to RTL simulation: **~0.001-0.01 MIPS**.

**Key concepts:**
- **Generic Payload:** Standardized transaction object (address, command, data pointer, response status, byte enables, streaming width)
- **Sockets:** `tlm_initiator_socket<>` and `tlm_target_socket<>` provide standardized port binding
- **Temporal Decoupling:** Initiators can run ahead of global time, synchronizing only at quantum boundaries. This is the primary mechanism for achieving high simulation throughput
- **DMI (Direct Memory Interface):** Allows initiators to get direct pointers to target memory, bypassing the transport mechanism entirely for even faster access

**Bridge between functional and RTL:** TLM-2.0 enables a spectrum of models. A common workflow:
1. Start with LT model for software development (100+ MIPS)
2. Refine interconnect to AT for performance analysis (1-10 MIPS)
3. Replace individual blocks with RTL (Verilator) for verification
4. Pin-level adapters bridge TLM sockets to RTL signal interfaces

**Evaluation for Simple:**
- Speed: Excellent at LT level (100-1000 MIPS)
- Accuracy: Configurable from functional to near-cycle-accurate
- Integration: C++ based, would require SFFI bridge from Simple
- Suitability: HIGH — the tiered abstraction model is exactly what a hybrid simulator needs

### 1.2 Verilator + SystemC Cosimulation

**How it works:** Verilator compiles Verilog/SystemVerilog RTL into C++ or SystemC SC_MODULE classes. In `--sc` mode, the generated model is a proper SystemC module that plugs directly into a SystemC simulation.

**Key details:**
- Pin type mapping: 1-bit → `bool`, 2-32 bits → `uint32_t`, 33-64 bits → `sc_bv`/`uint64_t`, wider → `sc_bv`
- Model internals are NOT pure SystemC (for performance). Only the pin interface uses SystemC signaling
- Using SystemC pin interconnect everywhere would reduce performance by **10x**
- Verilator is a **cycle-based** simulator (not event-driven). It removes all notions of time/delays and evaluates from one clock edge to the next
- Signal changes via VPI do NOT propagate immediately — `eval()` must be called explicitly

**Performance characteristics:**
- Verilator is **~500x faster** than Icarus Verilog (traditional event-driven simulator)
- Routinely beats commercial simulators in cycle-based simulation speed
- Supports multithreading for further speedup
- Optimization flags: `-O3 --x-assign fast --x-initial fast --no-assert` for best performance
- Profile-guided optimization available for thread assignment

**Chipyard benchmarks:**
- Software RTL simulation (Verilator/VCS): **O(1 KHz)** simulated clock frequency
- FPGA-accelerated (FireSim): **O(100 MHz)** — 100,000x faster

**Evaluation for Simple:**
- Speed: Fast for RTL simulation but still slow compared to functional models (~1 KHz for full SoC)
- Accuracy: Cycle-accurate RTL
- Integration: Requires C++ compilation step; could be driven from Simple via generated C++ wrapper
- Suitability: MEDIUM — good for individual RTL block verification, not for full-system fast simulation

### 1.3 VPI (Verilog Procedural Interface)

**What it is:** IEEE 1364 standard C interface for accessing and controlling Verilog simulations at runtime.

**Capabilities:**
- Read/write signal values at runtime
- Register callbacks on value changes, time advances, simulation events
- Create system tasks and functions callable from Verilog (`$my_task`)
- Traverse the design hierarchy programmatically
- Force/release signal values

**Verilator VPI support:**
- Limited subset: inspection, examination, value change callbacks, depositing values to **public signals only**
- Must explicitly mark signals with `/* verilator public */` pragma
- VPI is **much slower** than direct C++ reference access (hundreds of instructions vs. a couple)
- Value changes don't propagate until `eval()` is called

**Evaluation for Simple:**
- Speed: Significant overhead per access
- Accuracy: Signal-accurate
- Integration: Standard C API, easy to wrap via SFFI
- Suitability: LOW for performance-critical paths, useful for debug/instrumentation

### 1.4 DPI-C (Direct Programming Interface)

**What it is:** SystemVerilog standard (IEEE 1800) for direct function calls between SystemVerilog and C/C++/SystemC.

**Two directions:**
- **Import functions:** C functions callable from SystemVerilog. Execute in zero simulation time. Can have input/output/inout arguments.
- **Export functions:** SystemVerilog functions callable from C. Allow foreign code to invoke HDL functionality.

**Key properties:**
- Imported functions complete instantly (zero simulation time)
- Imported **tasks** can consume simulation time
- Memory management boundary: each side manages its own allocations
- Data type mappings are well-defined (bit, logic, byte, int, real, string, etc.)
- Much faster than VPI for function-call-style interaction

**Evaluation for Simple:**
- Speed: Minimal overhead for function calls
- Accuracy: Transaction-level (per function call)
- Integration: C ABI, straightforward SFFI binding
- Suitability: HIGH for hooking external models into RTL simulation

### 1.5 FMI/FMU (Functional Mockup Interface)

**What it is:** FMI 3.0 is a tool-independent standard for exchange and co-simulation of dynamic models. An FMU (Functional Mockup Unit) is a zip file containing a model description XML and compiled shared libraries.

**Three interface types:**
1. **Model Exchange (ME):** FMU provides model equations; external solver advances time. FMU has no internal solver.
2. **Co-Simulation (CS):** FMU contains both model AND solver. Data exchange only at discrete communication points. The co-simulation master algorithm coordinates FMUs.
3. **Scheduled Execution (SE):** New in FMI 3.0. External scheduler triggers model partitions based on clocks. Designed for real-time and ECU integration.

**Co-simulation key concepts:**
- Communication points `t_i` are the only synchronization moments
- Between communication points, each FMU solves independently
- This introduces communication delay (no instantaneous feedthrough between FMUs)
- The master algorithm controls: time advancement, data exchange, clock triggering, event handling
- **Intermediate Update Mode** allows finer-grained communication within a step
- Supports state save/restore for rollback-based algorithms

**FMI 3.0 new features:**
- Clocks (triggered, periodic, changing, countdown, aperiodic)
- Array variables with serialization
- Binary data type
- Terminal and icon support
- Intermediate update mode
- Scheduled execution for RTOS-like partitioning

**Evaluation for Simple:**
- Speed: Depends on FMU internal solver; typically good for control/analog co-simulation
- Accuracy: Depends on step size and FMU fidelity
- Integration: C API with XML configuration; well-suited for wrapping
- Suitability: LOW for digital RTL simulation (designed for continuous/hybrid systems), but HIGH for integrating analog/control models alongside digital simulation

### 1.6 QEMU + Verilator Cosimulation

**How it works:** QEMU provides fast functional CPU emulation (via TCG or KVM). Verilator provides cycle-accurate RTL simulation of specific peripherals or accelerators. A bridge connects QEMU's memory-mapped I/O to Verilator's signal-level interface.

**Architecture pattern:**
```
QEMU (CPU + memory + basic devices)
  |
  |--- MMIO bridge (shared memory or socket)
  |
  Verilator (RTL peripheral: GPU, crypto, custom accelerator)
```

**Synchronization approaches:**
1. **Lock-step:** QEMU advances one instruction, Verilator advances corresponding cycles. Slow but accurate.
2. **Quantum-based:** QEMU runs ahead by N instructions, then synchronizes with Verilator. Faster but may miss timing-dependent behavior.
3. **Interrupt-driven:** Verilator signals QEMU when events occur (interrupts, DMA completion). QEMU polls or uses callbacks.

**Renode approach:** Renode (by Antmicro) is a multi-node embedded system simulator that supports Verilator co-simulation for individual peripherals. HDL models compiled with Verilator can be attached to Renode's simulated bus, allowing RTL-accurate peripheral models within a functional system simulation.

**Evaluation for Simple:**
- Speed: CPU runs at QEMU speed (~100-1000 MIPS), peripherals at RTL speed
- Accuracy: Functional CPU + cycle-accurate peripherals
- Integration: Complex — requires bridge infrastructure
- Suitability: MEDIUM — good reference architecture for hybrid simulation

---

## 2. Fast Mode / RTL Mode Switching

### 2.1 Commercial Simulator Approaches

**Synopsys VCS and Cadence Xcelium** both support multi-abstraction simulation:

- **Mixed-signal simulation:** Digital RTL + analog SPICE in one simulation
- **Transaction-level / RTL co-simulation:** TLM models at system level, RTL for blocks under verification
- **Emulation integration:** VCS can offload to Synopsys ZeBu or Cadence Palladium hardware emulators
- **Fast functional mode:** Some simulators support a "fast functional" compile mode that strips timing but keeps behavior

### 2.2 Fast-Forward + Checkpoint + Switch (The gem5 Approach)

**gem5's KVM fast-forward** is the gold standard for this pattern:

1. **KVM Phase:** Use hardware virtualization (KVM) to run the target workload at **near-native speed** (GHz). No architectural statistics collected. Used to fast-forward through boot, initialization, uninteresting phases.
2. **Checkpoint:** Save complete machine state (registers, memory, TLB, caches) to disk.
3. **Restore + Switch:** Restore from checkpoint into a detailed timing model (MinorCPU, O3CPU). Collect accurate statistics for the region of interest.

**gem5 CPU model hierarchy (speed vs accuracy):**

| Model | Type | Speed | Accuracy | Use Case |
|-------|------|-------|----------|----------|
| **KVMCPU** | Hardware virtualization | ~GHz (native) | Functional only | Fast-forward, boot |
| **AtomicSimpleCPU** | Functional, in-order | ~100 MIPS | Functional + memory timing | Warm-up, cache population |
| **TimingSimpleCPU** | Functional, timing memory | ~10 MIPS | Memory timing accurate | Simple timing studies |
| **MinorCPU** | In-order pipeline (4 stages) | ~1-5 MIPS | Cycle-approximate | In-order core modeling |
| **O3CPU** | Out-of-order pipeline | ~0.1-1 MIPS | Cycle-accurate (microarch) | Detailed performance analysis |

**Checkpoint details:**
- Serializes all SimObjects (CPU state, memory, caches, etc.)
- Can restore with a **different CPU model** than was used to create the checkpoint
- Useful for: KVM → checkpoint → O3CPU (detailed analysis of specific code region)
- `--restore-with-cpu <CPU Type>` flag enables switching

### 2.3 Sampled Simulation (SimPoint, SMARTS)

**SimPoint:**
- Analyzes program execution to identify **representative phases** (basic block vectors)
- Uses clustering (k-means) to find a small number of simulation points
- Each simulation point represents a large portion of execution
- Simulate only the representative points; extrapolate full program behavior
- Reduces simulation time by **orders of magnitude** while maintaining <3% error for most benchmarks

**SMARTS (Systematic Sampling):**
- Statistical sampling approach
- Run fast (functional) for N instructions, then detailed for M instructions
- Repeat across the entire execution
- Uses confidence intervals to determine when enough samples have been collected
- Achieves ~1-3% error with only 0.01% of instructions simulated in detail

### 2.4 FireSim (FPGA-Accelerated)

**Architecture:**
- Takes Chisel/Verilog RTL design
- Applies **MIDAS** transformation: decouples target time from host time
- Synthesizes the transformed design onto FPGAs (AWS F1 or on-prem Xilinx Alveo)
- Adds hardware models for DRAM (timing-accurate), network, disk, UART
- Result: **cycle-exact RTL simulation at 10-100 MHz**

**Key properties:**
- Same RTL that would go to ASIC fabrication
- DRAM timing model runs as hardware on the FPGA alongside the design
- Network model enables datacenter-scale simulation (hundreds of nodes)
- Multi-hour FPGA compilation time
- Poorer debug visibility than software simulation (limited waveform capture)
- Used by 35+ institutions, 85+ peer-reviewed publications
- Has been used for development of commercially-available silicon

**Evaluation for Simple:**
- Speed: Exceptional (10-100 MHz vs 1 KHz for software RTL sim)
- Accuracy: Cycle-exact RTL
- Integration: Requires FPGA hardware and complex toolchain
- Suitability: LOW for initial implementation, HIGH as a future acceleration target

---

## 3. Timing Models for RISC-V

### 3.1 Pipeline Timing for RV32I

**Standard 5-stage in-order pipeline:**

| Stage | Function | Key Timing Aspects |
|-------|----------|-------------------|
| **Fetch (IF)** | Read instruction from I-cache | I-cache hit: 1 cycle; miss: 10-100 cycles. Fetch width: 1-4 instructions |
| **Decode (ID)** | Decode instruction, read registers | Register file read. Hazard detection. 1 cycle |
| **Execute (EX)** | ALU operation, address calculation | ALU: 1 cycle. MUL: 3-5 cycles. DIV: 10-40 cycles |
| **Memory (MEM)** | D-cache access for loads/stores | D-cache hit: 1 cycle; miss: 10-100 cycles. TLB miss: 10-100 cycles |
| **Writeback (WB)** | Write result to register file | 1 cycle |

**Pipeline hazards affecting timing:**
- **Data hazards:** RAW (Read After Write) — resolved by forwarding (0-cycle penalty) or stalling (1-2 cycle penalty)
- **Control hazards:** Branch/jump — penalty depends on branch prediction accuracy and pipeline depth
- **Structural hazards:** Resource conflicts (e.g., single-ported memory) — stall until resource available

**CPI (Cycles Per Instruction) for RV32I (reference from PicoRV32):**
- ALU register+immediate: 3 CPI
- ALU register+register: 3 CPI
- Branch (not taken): 3 CPI
- Branch (taken): 5 CPI
- Memory load: 5 CPI
- Memory store: 5 CPI
- Indirect jump (JALR): 6 CPI
- Shift operations: 4-14 CPI (without barrel shifter)
- With barrel shifter: shifts become 3 CPI (same as ALU)
- Dhrystone benchmark: ~4.1 average CPI → 0.516 DMIPS/MHz

### 3.2 Branch Prediction Modeling

**Predictor types (from MARSS-RISCV's configurable models):**
- **Bimodal:** 2-bit saturating counters indexed by PC. Simple, ~85% accuracy
- **2-level adaptive (Gshare):** XOR of global history register with PC to index PHT. ~92-95% accuracy
- **2-level adaptive (GAg, GAp, PAg, PAp, Gselect):** Various combinations of global/per-address history with global/per-address pattern tables
- **Return Address Stack (RAS):** Dedicated stack for call/return prediction. Near-perfect for well-structured code
- **Tournament predictor:** Meta-predictor chooses between two predictors based on recent accuracy

**Timing impact:**
- Correct prediction: 0-cycle penalty (fetched correct path)
- Misprediction: Pipeline flush = pipeline-depth cycles penalty (5 cycles for 5-stage, 15+ for deep OoO)
- Branch prediction is the single largest source of performance variation in pipelines deeper than 5 stages

### 3.3 Memory Latency Modeling

**Cache hierarchy timing (typical):**
| Level | Hit Latency | Miss Penalty | Typical Size |
|-------|-------------|--------------|--------------|
| L1 I-cache | 1-2 cycles | 10-20 cycles | 16-64 KB |
| L1 D-cache | 1-2 cycles | 10-20 cycles | 16-64 KB |
| L2 unified | 5-12 cycles | 50-200 cycles | 128 KB - 2 MB |
| L3 (if present) | 20-40 cycles | 100-300 cycles | 2-32 MB |
| DRAM | N/A | 50-200 ns (100-400 cycles @ 2 GHz) | GBs |

**DRAM timing models available:**
- **Fixed latency:** Simple model, constant delay per access. Fast simulation. (MARSS-RISCV base model)
- **DRAMSim3:** Cycle-accurate DRAM controller + timing model. Supports DDR3/DDR4/LPDDR4/HBM2. Integrated with MARSS-RISCV.
- **Ramulator/Ramulator2:** Cycle-accurate, modular DRAM simulator from CMU SAFARI. Supports DDR3/DDR4/DDR5/LPDDR5/HBM2/HBM3. Integrates with gem5 as a library.

**TLB timing:**
- TLB hit: 0-1 cycles (typically overlapped with cache access)
- TLB miss: Page table walk = multiple memory accesses (2-5 for Sv32, 3-5 for Sv39)
- Hardware page table walker: 10-100 cycles per walk depending on cache state

### 3.4 Approximating Timing Without Full RTL

**Instruction-accurate vs cycle-accurate vs timing-approximate:**

| Approach | What It Models | Speed | Error |
|----------|---------------|-------|-------|
| **Instruction-accurate** | Correct ISA execution, no timing | 100-1000 MIPS | No timing info |
| **Timing-approximate (IPC model)** | Fixed CPI per instruction class + cache miss model | 10-100 MIPS | 5-20% vs real HW |
| **Cycle-approximate (pipeline model)** | Simplified pipeline + caches + branch predictor | 1-10 MIPS | 2-10% vs real HW |
| **Cycle-accurate (microarch model)** | Detailed pipeline, OoO, precise memory | 0.1-1 MIPS | <2% vs real HW |
| **RTL simulation** | Gate-level behavior | 0.001 MIPS (1 KHz SoC) | Exact (by definition) |

**Recommended approach for Simple:** Start with **timing-approximate** model:
1. Maintain a cycle counter alongside functional execution
2. Add fixed costs per instruction class (from a CPI table)
3. Model cache behavior with a simple set-associative cache simulator
4. Add branch misprediction penalties based on a bimodal predictor
5. This achieves ~10% accuracy at ~50 MIPS — good enough for software development and initial performance tuning

---

## 4. Hybrid Simulator Projects

### 4.1 gem5

**Overview:** Open-source discrete-event full-system simulator. Written in C++/Python. BSD-3 license.

**CPU models (detailed in Section 2.2):**
- AtomicSimpleCPU → TimingSimpleCPU → MinorCPU → O3CPU (increasing detail)
- KVMCPU for hardware-accelerated fast-forward
- Can switch between models at runtime via checkpoints

**MinorCPU pipeline (configurable in-order):**
```
Fetch1 (I-cache fetch) → Fetch2 (line→instruction) → Decode (instruction→micro-op) → Execute (ALU + LSQ)
```
- Configurable pipeline widths and latencies
- Models branch prediction with configurable predictor
- LSQ (Load Store Queue) for memory operations
- Forwards data between stages

**O3CPU pipeline (out-of-order):**
```
Fetch → Decode → Rename → Issue/Execute/Writeback → Commit
```
- Physical register file with free list
- Instruction queue with wake-up/select logic
- Reorder buffer for in-order commit
- Handles serializing instructions, branch misprediction recovery

**Memory system:**
- Port-based architecture: master ports (initiators) connect to slave ports (targets)
- Request/response protocol with timing
- Configurable cache hierarchy (L1/L2/L3, coherence protocols)
- Integrates with Ramulator2 for DRAM timing

**ISA support:** x86, ARM, RISC-V, SPARC, MIPS, POWER

**Evaluation for Simple:**
- Speed: 0.1-100 MIPS depending on CPU model
- Accuracy: Best-in-class for academic microarchitecture research
- Integration: Complex C++/Python codebase (1M+ lines). Very hard to integrate with Simple directly.
- Suitability: HIGH as a reference architecture and comparison point. Study its design for inspiration but don't try to embed it.

### 4.2 Renode

**Overview:** Open-source multi-node embedded system simulation framework by Antmicro. Written in C#/.NET.

**Key features:**
- Simulates complete embedded systems: CPU + peripherals + external connections
- Supports multiple architectures: ARM Cortex-M/A/R, RISC-V, SPARC, Xtensa, POWER
- Multi-node: simulate networks of devices communicating via UART, SPI, I2C, Ethernet, CAN, etc.
- **Verilator co-simulation:** HDL peripheral models compiled with Verilator can be connected to Renode's simulated bus
- Robot Framework integration for automated testing
- GDB stub for debugging

**Cosimulation architecture:**
- Renode simulates CPU functionally (instruction-accurate, no cycle-level timing)
- Individual peripherals can be: C# models (fast), Verilator RTL (accurate), or Python models (flexible)
- Communication via shared memory or sockets between Renode and Verilator processes

**Evaluation for Simple:**
- Speed: ~10-100 MIPS for functional CPU simulation
- Accuracy: Functional CPU + selectable peripheral accuracy
- Integration: C#/.NET based — harder to integrate with Simple than C-based tools
- Suitability: MEDIUM — good reference for multi-node peripheral cosimulation pattern

### 4.3 SimEng (University of Bristol)

**Overview:** Modern cycle-accurate processor simulation framework. Written in C++.

**Key features:**
- Designed for **performance and scalability**
- Supports scalar to superscalar out-of-order designs
- Currently supports AArch64; RISC-V and x86 planned
- Clean, modern C++ codebase
- Emphasis on being easy to modify and configure
- SST (Structural Simulation Toolkit) integration for memory system modeling

**Evaluation for Simple:**
- Speed: Designed to be fast (claims competitive with gem5)
- Accuracy: Cycle-accurate processor modeling
- Integration: Modern C++ with clean API
- Suitability: MEDIUM — good design reference but AArch64-only currently

### 4.4 MARSS-RISCV

**Overview:** Full-system cycle-level RISC-V microarchitectural simulator built on TinyEMU.

**Architecture (critical for Simple's design):**
- **Functional layer:** TinyEMU emulator provides: RISC-V CPU state, physical memory, MMU, I/O devices, bootloader, kernel support
- **Microarchitectural layer:** Cycle-level models overlaid on functional emulation
- **Mode switching:** Can switch between functional (fast) and cycle-level (detailed) simulation at runtime

**Microarchitectural models:**
- **In-order pipeline:** Configurable stages, forwarding, stalling
- **Out-of-order pipeline:** Issue queue, ROB, register renaming
- **Branch predictor:** Bimodal, Gshare, Gselect, GAg, GAp, PAg, PAp + RAS
- **Cache hierarchy:** Configurable L1I/L1D/L2, various allocation policies
- **TLBs:** Separate for code, loads, stores
- **DRAM:** Fixed-delay base model + DRAMSim3 + Ramulator integration

**ISA support:** RV32GC and RV64GC (user ISA v2.2, privileged v1.10)

**Configuration:** Single JSON file for all parameters

**Evaluation for Simple:**
- Speed: Functional mode ~100 MIPS; cycle-level mode ~1-10 MIPS
- Accuracy: Cycle-level with configurable microarchitecture
- Integration: C codebase, small and hackable
- Suitability: **HIGHEST** — closest to what Simple needs. The TinyEMU-based architecture (functional emulator + cycle-level overlay) is the ideal pattern.

### 4.5 Chipyard

**Overview:** UC Berkeley's integrated SoC design, simulation, and implementation framework.

**Simulation stack:**
1. **Software RTL (Verilator/VCS):** O(1 KHz). Full waveforms. Quick compile.
2. **FPGA-accelerated (FireSim):** O(100 MHz). Cycle-exact. Multi-hour compile.

**Key value:** Chipyard provides the RTL generators (Rocket, BOOM) that produce the RISC-V designs. FireSim then simulates them at FPGA speed. The RTL is identical to what goes to fabrication.

**Evaluation for Simple:**
- Speed: 1 KHz (software) to 100 MHz (FPGA)
- Accuracy: Cycle-exact RTL
- Integration: Scala/Chisel + complex build system
- Suitability: LOW for direct integration, HIGH as reference for RTL simulation infrastructure

### 4.6 DRAMSim3 / Ramulator2

**Ramulator2** (CMU SAFARI):
- Modular, extensible, cycle-accurate DRAM simulator
- Supports DDR3/DDR4/DDR5/LPDDR3/LPDDR4/LPDDR5/HBM2/HBM3/GDDR6
- gem5 integration via shared library (`libramulator.so`)
- Verified against Micron's Verilog DRAM model
- YAML configuration
- ~10x faster than Ramulator 1.0

**DRAMSim3:**
- Cycle-accurate DRAM simulator
- Supports DDR3/DDR4/LPDDR3/LPDDR4/HBM2
- Integrated with MARSS-RISCV
- Simulates controller, rank, bank, timing constraints

**Evaluation for Simple:**
- Both provide drop-in DRAM timing models
- Ramulator2 is newer, faster, more standards
- Can be integrated as a library for memory access timing

---

## 5. RTL Concepts for IR Design

### 5.1 RTL Primitives Needed

**Combinational logic:**
- `wire` — continuous assignment, no storage
- `always_comb` / `assign` — combinational process, re-evaluates when inputs change
- Operators: AND, OR, XOR, NOT, MUX, arithmetic, shift, comparison
- No clock dependency

**Sequential logic:**
- `reg` / `logic` — storage elements
- `always_ff @(posedge clk)` — synchronous, clocked process
- `always_ff @(posedge clk or posedge rst)` — async reset
- Flip-flop: single-bit storage, updates on clock edge
- Register: multi-bit flip-flop group

**Infrastructure signals:**
- `clock` — periodic signal driving sequential logic
- `reset` — initialization signal (synchronous or asynchronous)
- `enable` — conditional update gating

**Structural:**
- Module instantiation (hierarchy)
- Port connections (input, output, inout)
- Generate blocks (parameterized instantiation)

### 5.2 Event-Driven vs Cycle-Based Simulation

**Event-driven simulation (Icarus Verilog, VCS, Xcelium):**
- Maintains a global **event queue** sorted by time
- Each event = (time, signal, new_value)
- **Delta cycles:** Multiple events at the same simulation time are resolved iteratively until stable
- Sensitivity lists determine which processes wake up when signals change
- Handles delays, glitches, race conditions accurately
- Supports behavioral constructs: `#delay`, `@(event)`, `wait(condition)`
- **Speed:** Slow — must process every signal change individually

**Cycle-based simulation (Verilator, CXXRTL):**
- Removes all timing information
- Evaluates the entire design from one clock edge to the next
- Topologically sorts combinational logic to evaluate in correct order
- **No delta cycles** — evaluates everything in one pass per clock edge
- Only supports synthesizable RTL (no delays, no behavioral constructs)
- **Speed:** 100-500x faster than event-driven for synthesizable designs

**Hybrid approaches:**
- Some simulators use cycle-based for synchronous logic, event-driven for async
- CXXRTL (from Yosys) provides a middle ground: C++ simulation with optional debug features

### 5.3 IR Design Implications

For a Simple-language RTL IR, the key design decisions are:

1. **Cycle-based evaluation** is strongly recommended for performance
2. IR needs to distinguish: combinational assignments vs sequential (clocked) updates
3. Need a topological sort of combinational dependencies
4. Sequential elements update in two phases: read old values, compute new values, then commit all updates simultaneously (mimics real hardware behavior)
5. Clock and reset should be explicit signals, not implicit
6. Module hierarchy should map to the IR's module system

---

## 6. Comprehensive Comparison

### Speed Comparison

| Approach | Simulation Speed | Equivalent MIPS | Relative |
|----------|-----------------|-----------------|----------|
| Native execution (KVM) | GHz | ~1,000,000 | 1,000,000x |
| QEMU TCG (functional) | 100-1000 MIPS | 100-1000 | 100-1000x |
| TLM Loosely-Timed | 100-1000 MIPS | 100-1000 | 100-1000x |
| Functional interpreter | 10-100 MIPS | 10-100 | 10-100x |
| Timing-approximate | 10-50 MIPS | 10-50 | 10-50x |
| TLM Approximately-Timed | 1-10 MIPS | 1-10 | 1-10x |
| gem5 MinorCPU | 1-5 MIPS | 1-5 | 1-5x |
| MARSS-RISCV cycle-level | 1-10 MIPS | 1-10 | 1-10x |
| gem5 O3CPU | 0.1-1 MIPS | 0.1-1 | **baseline** |
| FireSim (FPGA) | 10-100 MHz clock | 10-100 MIPS equiv | 10-100x |
| Verilator (full SoC RTL) | ~1 KHz clock | ~0.001 MIPS | 0.001x |
| Icarus Verilog | ~2 Hz clock | ~0.000002 MIPS | 0.000002x |

### Accuracy vs Speed Trade-off

```
Speed (log scale)
  |
  |  KVM/Native ●
  |                    ← Functional (no timing)
  |  QEMU TCG ●   TLM-LT ●
  |                    ← Transaction-level timing
  |  Timing-approx ●
  |                    ← Approximate pipeline timing
  |  TLM-AT ●   MinorCPU ●   MARSS-cycle ●
  |                    ← Cycle-approximate
  |  O3CPU ●
  |                    ← Cycle-accurate (microarch)
  |  FireSim ●
  |                    ← Cycle-exact RTL (FPGA)
  |  Verilator ●
  |                    ← Cycle-exact RTL (software)
  |  Icarus ●
  |                    ← Event-accurate RTL
  +----------------------------------------→ Accuracy
     None    Approx   Cycle    RTL-exact
```

### Integration Complexity

| Approach | Language | Lines of Code | Integration Effort |
|----------|----------|---------------|-------------------|
| Custom timing-approx model | Simple | ~2,000 | LOW |
| MARSS-RISCV integration | C | ~15,000 | MEDIUM |
| Verilator wrapper | C++ | ~500 wrapper + RTL | MEDIUM |
| gem5 integration | C++/Python | ~1,000,000+ | VERY HIGH |
| FireSim | Scala/Chisel/C++ | ~500,000+ | VERY HIGH |
| FMI/FMU wrapper | C | ~1,000 | LOW-MEDIUM |
| SystemC TLM model | C++ | ~5,000-20,000 | MEDIUM-HIGH |

---

## 7. Recommendations

### Recommended Architecture for Simple

Based on the research, the optimal architecture for Simple's simulator is a **three-tier hybrid** inspired by MARSS-RISCV's design and gem5's mode-switching:

#### Tier 1: Fast Functional Mode (default)
- **Purpose:** Software development, debugging, boot, general execution
- **Speed target:** 50-200 MIPS
- **Implementation:** Direct interpreter or compiled execution of RISC-V instructions
- **Timing:** None, or simple instruction-counting (IPC=1 assumption)
- **What to model:** Correct ISA execution, memory, I/O devices functionally

#### Tier 2: Timing-Approximate Mode
- **Purpose:** Performance estimation, cache analysis, quick profiling
- **Speed target:** 5-50 MIPS
- **Implementation:** Functional execution + timing annotations
- **Timing model components:**
  - CPI table per instruction class
  - Set-associative cache simulator (L1I, L1D, optional L2)
  - Bimodal branch predictor with misprediction penalty
  - Fixed DRAM latency model
  - TLB with page table walk cost
- **Accuracy:** ~10-15% of real hardware performance numbers
- **Key advantage:** Only 2,000-3,000 lines of Simple code beyond Tier 1

#### Tier 3: Cycle-Accurate Mode
- **Purpose:** Detailed microarchitectural analysis, RTL correlation
- **Speed target:** 0.5-5 MIPS
- **Implementation:** Detailed pipeline model overlaid on functional execution (MARSS-RISCV pattern)
- **Pipeline model:** Configurable in-order (5-stage) or out-of-order
- **Memory model:** Cycle-accurate cache hierarchy + Ramulator2 for DRAM (via SFFI)
- **Branch predictor:** Configurable (bimodal, Gshare, tournament)
- **Accuracy:** <5% of real hardware

#### Mode Switching
- Support **checkpoint/restore** between tiers (inspired by gem5)
- Switch granularity: per-function, per-region-of-interest, or per-instruction-count
- Tier 1 → Tier 2: Add timing annotations without re-execution
- Tier 2 → Tier 3: Warm up caches from Tier 2 state, then simulate in detail
- Tier 3 → Tier 1: Discard microarchitectural state, continue functional execution

#### RTL Cosimulation (Optional Future)
- **Verilator integration** via C++ wrapper (SFFI from Simple)
- Use for: individual peripheral RTL verification against functional model
- Pattern: Simple functional CPU + Verilator RTL peripheral (like Renode)
- DPI-C for function-call interface, VPI for signal-level debug only

#### Key Design Decisions

1. **Build Tier 2 first** — it provides the best speed/accuracy/effort ratio
2. **Use the MARSS-RISCV overlay pattern** — functional emulator as base, timing models layered on top, rather than a separate timing-only simulator
3. **Implement in Simple** where possible, SFFI to C for DRAM models (Ramulator2) and RTL cosimulation (Verilator)
4. **Single configuration format** (SDN, per project conventions) for all microarchitectural parameters
5. **FMI/FMU** is not recommended for the core simulator but could be useful later for analog/mixed-signal cosimulation
6. **Sampled simulation (SimPoint)** should be implemented once Tier 3 exists — it is the standard technique for making cycle-accurate simulation tractable for large workloads

### Implementation Priority

| Priority | Component | Effort | Impact |
|----------|-----------|--------|--------|
| 1 | Tier 1: Functional RISC-V execution | Already exists (SimpleOS) | Foundation |
| 2 | Tier 2: CPI table + cache model | ~2 weeks | Enables performance estimation |
| 3 | Tier 2: Branch predictor model | ~3 days | Improves Tier 2 accuracy |
| 4 | Tier 2: TLB + page walk model | ~3 days | Completes memory hierarchy |
| 5 | Checkpoint/restore infrastructure | ~1 week | Enables mode switching |
| 6 | Tier 3: In-order pipeline model | ~2 weeks | Cycle-accurate analysis |
| 7 | Verilator SFFI bridge | ~1 week | RTL peripheral cosim |
| 8 | Ramulator2 SFFI integration | ~1 week | Accurate DRAM timing |
| 9 | Tier 3: Out-of-order model | ~3 weeks | Advanced microarch studies |
| 10 | SimPoint sampling support | ~1 week | Tractable long workloads |

---

## Sources

- SystemC/TLM: IEEE 1666-2011, Accellera SystemC, TLM-2.0 standard
- Verilator: verilator.org documentation (v5.047)
- VPI: IEEE 1364 standard, Wikipedia
- DPI-C: IEEE 1800 SystemVerilog standard, Wikipedia
- FMI: fmi-standard.org FMI 3.0 specification
- gem5: gem5.org documentation (CPU models, memory system, KVM, checkpoints)
- FireSim: fires.im, Chipyard documentation
- Chipyard: chipyard.readthedocs.io (v1.11.0)
- MARSS-RISCV: github.com/bucaps/marss-riscv
- SimEng: github.com/UoB-HPC/SimEng
- Ramulator2: github.com/CMU-SAFARI/ramulator2
- Renode: renode.readthedocs.io, renode.io
- PicoRV32: CPI benchmarks from github.com/YosysHQ/picorv32
- CVA6: OpenHW Group CVA6 user manual
- Discrete Event Simulation: Wikipedia
- RTL: Wikipedia Register-transfer level
