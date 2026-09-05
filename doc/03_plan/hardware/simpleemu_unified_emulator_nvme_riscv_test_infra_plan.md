# SimpleEMU: Fast Behavioral-to-RTL Emulator, Unified NVMe Firmware, Simple RISC-V Production Debug, and Advanced Test-Artifact Infrastructure

**Date:** 2026-09-01
**Status:** Proposed architecture and staged implementation plan
**Primary repositories audited:**
- `ormastes/simple` at `02b81d21c9de44c8d53ed5edb4ca473f61129d95`
- `ormastes/simple-riscv` at `3a1414ff77d166e48d77d6848a586ac2179492bf`
- `ormastes/simple-mllvm-qemu-rtl` at `b65c7cf5a05ad55b18016433fcdcaf18b8fb9d9a`
- `ormastes/simple-qemu` at its 2026-09-01 `main`

**Related plan:** `nvme_ssd_firmware_hardening_design_plan.md` defines the deeper controller/media portability, semantic typing, embedded Promise, index-handle allocator, NAND isolation, and illegal-access hardening design. This document integrates that work into one emulator-to-silicon execution and verification stack.

---

## 1. Executive decision

Build one product-facing **SimpleEMU** infrastructure with independent fidelity, scheduling, and evidence axes:

```text
Fidelity
  native behavioral -> native timed -> ISA interpreter -> ISA DBT
  -> timing model -> hybrid RTL -> full RTL -> FPGA -> silicon

Scheduling
  deterministic single -> deterministic parallel -> schedule exploration
  -> native host-parallel/non-deterministic

Evidence
  SSpec intent -> machine-readable test pack -> target projection
  -> raw evidence -> canonical comparison -> result/coverage pack
  -> Markdown/manual projection
```

The most important decisions are:

1. **One canonical NVMe firmware source closure.** There must not be a host-only fake firmware and a separately rewritten RV32 firmware. Native x86/AArch64 behavioral builds and RISC-V firmware builds compile the same firmware modules and monomorphized behavior. Configuration and statically selected providers may differ; command processing, FTL, recovery, allocation, async state machines, and safety checks may not.
2. **One exact firmware payload from ISA emulation through silicon.** ISA interpreter, DBT, timing, hybrid RTL, full RTL, FPGA, and physical board qualification execute the same RISC-V ELF payload bytes. Packaging may add signatures or boot metadata, but the measured firmware payload hash remains identical.
3. **No dummy behavior in the certified source or provider graph.** A missing capability is a compile-time/profile error or an explicit `Unsupported` result. It must never become a no-op, constant success, silent zero, host-array mutation, or alternate short path.
4. **Keep `@reg`/register attributes and AOP.** Register attributes lower to explicit HIR/MIR register effects. AOP verifies legal ownership and access paths, while generated accessors remain the hot path. AOP must not add a runtime callback to every ordinary field access.
5. **Use native behavioral execution for throughput, not as proof of ISA correctness.** It is the fastest functional and concurrency test tier. The ISA/RTL tiers remain required for architectural and implementation correctness.
6. **Use deterministic parallelism as a normal mode.** Parallel host workers may execute independent partitions, but architectural commits follow a canonical event order. A separate native host-parallel mode intentionally retains OS-scheduler nondeterminism for race stress and performance profiling.
7. **Make SSpec machine-readable-first.** Markdown is a projection, not the canonical test product. One SSpec scenario should emit reusable transaction streams, pin vectors, timing/fault schedules, oracles, coverage intent, traces, and result manifests for behavioral simulation, DBT, RTL, FPGA, board, and applicable ATE functional testing.
8. **Do not confuse functional vectors with ATPG.** Functional scenarios and pin vectors can be projected across logic simulation, FPGA, board, and ATE. Scan ATPG patterns are generated from a scan-inserted netlist by ATPG tools; SSpec can configure, package, schedule, compare, and trace those patterns, but must not claim to replace ATPG.

### 1.1 Product boundary

The recommended ownership boundary is:

| Repository | Long-term ownership |
|---|---|
| `simple` | compiler, HWIR, RegisterIR, PinIR, effect/AOP verification, SSpec, test-artifact schemas, CLI integration |
| `simple-mllvm-qemu-rtl` | execution engines, DBT, machine runtime, virtual time, device framework, timing and RTL adapters; expose this publicly as **SimpleEMU** while retaining compatibility package names initially |
| `simple-riscv` | canonical RISC-V processor/SoC hardware product, generated RTL, board profiles, debug/trace, DFT hooks, FPGA/silicon qualification |
| `simple-qemu` | external QEMU runner/oracle and compatibility evidence only; it is not the in-house emulator core |
| `simpleos_nvme_fw` inside `simple` initially | canonical firmware source; later extract only after source-closure parity and stable package interfaces exist |

The richer RISC-V RTL and debug sources currently resident in `simple` and the historical handwritten content in `simple-riscv` must not remain competing product implementations. Migrate toward one canonical hardware package in `simple-riscv`; `simple` should consume it through a pinned package/submodule contract and own the language/compiler infrastructure.

---

## 2. Non-negotiable invariants

### 2.1 Firmware identity invariants

- Every firmware function in the certified closure has one source definition.
- Native behavioral and RISC-V builds have identical normalized monomorphized MIR for target-independent functions.
- ISA/timing/RTL/FPGA/silicon runs consume the same firmware payload digest.
- No core module tests `is_simulator`, `host_build`, `fake_media`, or an equivalent condition.
- No test imports, fault hooks, or emulator backing arrays are reachable from the production firmware dependency graph.
- Profile selection is static and appears in a signed/build-bound capability manifest.
- An unavailable provider fails the build or boot qualification; it never falls back to a simulation provider.

### 2.2 Register and hardware-access invariants

- Every SFR/register belongs to one generated `RegisterBlockId` and one access authority.
- Firmware accesses registers only through generated typed register accessors.
- Native behavioral execution forwards the same typed register effects to a behavioral SFR bank.
- ISA execution turns those effects into guest loads/stores and MMIO dispatch.
- RTL generation consumes the same RegisterIR to produce the register block and field semantics.
- Reserved-bit, read-only, write-only, W1C/W0C, read-to-clear, self-clear, shadow, alias, and reset behavior are declared once.
- Direct raw MMIO pointers, arbitrary volatile operations, and direct device-state mutation are rejected outside an explicitly privileged HAL capsule.

### 2.3 Scheduling invariants

- Deterministic modes define total event ordering independent of host thread completion order.
- Native non-deterministic mode is clearly labeled and cannot produce a deterministic certification result.
- Timing and RTL results are logically deterministic even when host workers execute evaluation in parallel.
- All externally visible device mutations enter through the central scheduler/commit protocol.
- WFI and polling-loop acceleration may skip host work but may not alter architecturally observable ordering.

### 2.4 Evidence invariants

- Every pass verdict names the exact source revision, compiler/tool versions, configuration hash, firmware hash, seed, schedule hash, and target identity.
- A text marker alone is never the authoritative oracle.
- Every visible result has positive evidence and a non-vacuity witness.
- Every critical gate has a sabotage/mutation that proves the gate turns red.
- Expected data is independent of the implementation under test.
- Raw evidence is immutable and content-addressed; Markdown can be regenerated from it.

---

## 3. Current-state audit

### 3.1 What already exists and should be retained

The current codebase has substantial pieces worth preserving:

- `simple-mllvm-qemu-rtl` already separates guest CPU definitions/decoders, IR_TC, optimization, native backend, runtime, timing, traces, and RTL bridge capsules.
- RV32/RV64, AVR, and 8086 guest decode structures exist.
- The optimizer already names constant folding, dead-code elimination, common-subexpression elimination, width narrowing, and TB chaining.
- `JitCache` already models guest-PC-keyed translation blocks, invalidation, range invalidation, and chaining.
- `GuestMemory` has address spaces and MMIO region descriptors.
- The hybrid plan already defines fast/timing/RTL modes, snapshot transfer, retirement traces, VCD output, and deterministic RTL phase ordering.
- `simple` already contains RV32/RV64 generated core, CSR, MMU/PMP, atomic, and RVFI-oriented sources beyond the older handwritten `simple-riscv` core.
- The hardware debug tree already contains JTAG TAP, DTM/DMI, debug module registers, system-bus access, OpenOCD, and GDB test infrastructure.
- The NVMe reference stack already has a broad host-simulation command/FTL/recovery/reliability surface and many negative tests.
- The modern SSpec evidence design already defines typed evidence requests, providers, adapters, comparators, selectors, manifests, and Markdown projection.

### 3.2 Truth-reset findings

| Area | Current evidence | Why it is not yet the target | Required action |
|---|---|---|---|
| External QEMU | `simple-qemu` wraps installed QEMU and collects summaries | useful oracle/runner, not own instruction/device engine | keep as external adapter; do not merge it with SimpleEMU internals |
| Fast RV32 mode | `HybridSimulator.step()` fetches one instruction, creates a builder/module, decodes, applies it, then repeats | this is per-instruction translation, not cached TB execution | build a real TB frontend, cache, dispatcher, chaining, and tiering |
| ELF loading | compatibility method treats "ELF bytes" as a raw image | wrong section placement, symbols, relocations, permissions, and entry point | add real ELF loader and immutable image manifest |
| MMIO | `GuestMemory` can register MMIO regions | ordinary width reads/writes shown still access raw backing memory directly | route every access through a page/region fast map with direct RAM and MMIO slow paths |
| I/O dispatch | manually tagged concrete arrays; unmapped reads may return `0xFF`; writes may be ignored | silent fallback and device-indexing fragility violate fail-closed behavior | generated device registry, typed IDs, access faults, and explicit unsupported policy |
| Native RTL | current engine stores named signal values and traces checkpoint fields | it does not yet elaborate/evaluate combinational and sequential processes | implement elaborated RTL IR, delta cycles, clock/reset domains, memory and assertions |
| AOP field access | `execution`, `within`, and `attr` exist | `get`, `set`, and `effect` selectors are still deferred | first lower register accesses into explicit effects; then add effect/get/set verification selectors |
| NVMe host firmware | broad functional simulation | explicitly not silicon firmware; still has stand-ins and simulation-only boundaries | unify source, replace stand-ins, add real controller/media/DRAM/DMA paths |
| RV32 firmware | scalar/no-array re-expression of many functions | separate implementation can drift and cannot prove production source | delete as a product implementation after canonical source compiles freestanding |
| Embedded async | file claims fixed/no-heap Promise/task support | uses dynamic-looking arrays/closures; Promise completion linkage is incomplete; unit spec is skipped | replace with fixed arenas, typed index handles, explicit poll/state IDs, wake tokens, active tests |
| RISC-V debug | GDB/OpenOCD path exercises a testbench fake hart | native `stepi`, real CSRs, executable memory, and full SBA widths await real-hart integration | bind DM to canonical RV32/RV64 cores and add debug compliance campaign |
| SSpec NAND capture | local helper writes a hexdump text file | explicitly a temporary stand-in; not typed reusable evidence | replace with Test Artifact Pack provider and binary/transaction/pin projections |

### 3.3 Current code references

- Main integration repo: <https://github.com/ormastes/simple/tree/02b81d21c9de44c8d53ed5edb4ca473f61129d95>
- Own emulation/RTL repo: <https://github.com/ormastes/simple-mllvm-qemu-rtl/tree/b65c7cf5a05ad55b18016433fcdcaf18b8fb9d9a>
- RISC-V product repo: <https://github.com/ormastes/simple-riscv/tree/3a1414ff77d166e48d77d6848a586ac2179492bf>
- Hybrid step implementation: <https://github.com/ormastes/simple-mllvm-qemu-rtl/blob/b65c7cf5a05ad55b18016433fcdcaf18b8fb9d9a/src/timing/hybrid_sim.spl>
- Guest memory implementation: <https://github.com/ormastes/simple-mllvm-qemu-rtl/blob/b65c7cf5a05ad55b18016433fcdcaf18b8fb9d9a/src/runtime/memory.spl>
- Current RTL signal engine: <https://github.com/ormastes/simple-mllvm-qemu-rtl/blob/b65c7cf5a05ad55b18016433fcdcaf18b8fb9d9a/src/rtl/sim_engine.spl>
- NVMe production boundary: <https://github.com/ormastes/simple/blob/02b81d21c9de44c8d53ed5edb4ca473f61129d95/examples/09_embedded/simpleos_nvme_fw/fw/PRODUCTION_STATUS.md>
- RV32 re-expression status: <https://github.com/ormastes/simple/blob/02b81d21c9de44c8d53ed5edb4ca473f61129d95/examples/09_embedded/simpleos_nvme_fw/fw_rv32/README.md>
- Debug gap: <https://github.com/ormastes/simple/blob/02b81d21c9de44c8d53ed5edb4ca473f61129d95/src/lib/hardware/debug/gdb_e2e.md>
- Temporary capture helper: <https://github.com/ormastes/simple/blob/02b81d21c9de44c8d53ed5edb4ca473f61129d95/test/03_system/app/nvme_firmware/nvme_nand_capture_spec.spl>

---

## 4. Target architecture

### 4.1 Overall system

```text
                       Source and specification plane
 ┌─────────────────────────────────────────────────────────────────────┐
 │ Simple firmware source  CoreConfig  BoardProfile  MediaProfile      │
 │ RegisterIR  PinIR  ProtocolIR  MemoryIR  TestIntentIR  OracleIR      │
 └──────────────────────────────┬──────────────────────────────────────┘
                                │ generated, hash-bound contracts
                                ▼
                         SimpleEMU machine plane
 ┌─────────────────────────────────────────────────────────────────────┐
 │ MachineGraph  AddressSpace  SfrBus  DmaFabric  IrqFabric             │
 │ VirtualTime  EventQueue  Clock/Reset  Fault/Power  Snapshot/Replay   │
 └──────────────────────────────┬──────────────────────────────────────┘
                                │ stable engine contract
          ┌─────────────────────┼─────────────────────────────┐
          ▼                     ▼                             ▼
  Native behavioral      ISA execution family          RTL family
  x86/AArch64/RV64       interpreter / IR_TC DBT       native / GHDL /
  direct source build    x86/AArch64/RV64 hosts        Verilator / FPGA
          └─────────────────────┼─────────────────────────────┘
                                ▼
                      Canonical observation plane
 ┌─────────────────────────────────────────────────────────────────────┐
 │ NVMe/PCIe/AXI/ONFI transactions, SFR effects, DMA, IRQ, RVFI/RVVI,  │
 │ timing events, pins, waveforms, state snapshots, faults, coverage   │
 └──────────────────────────────┬──────────────────────────────────────┘
                                ▼
                    SSpec comparison and projections
 ┌─────────────────────────────────────────────────────────────────────┐
 │ behavioral / DBT / timing / RTL / FPGA / board / ATE-functional     │
 │ result packs, differential reports, coverage, Markdown manuals       │
 └─────────────────────────────────────────────────────────────────────┘
```

### 4.2 Stable engine contract

Every CPU/RTL engine implements one bounded-run contract:

```simple
trait ExecutionEngine:
    fn load(image: ExecutableImage, machine: MachineBinding) -> Result<EngineId, LoadError>
    fn run(state: &mut MachineState, budget: ExecBudget) -> ExecExit
    fn snapshot(state: MachineState) -> EngineSnapshot
    fn restore(snapshot: EngineSnapshot) -> Result<(), RestoreError>
    fn capabilities() -> EngineCapabilities
```

`ExecBudget` contains both an instruction/work budget and the next virtual-time deadline. `ExecExit` is a closed sum type:

```text
BudgetExpired | BranchDispatch | Mmio | Trap | Interrupt | Halt | Wfi
| Breakpoint | Watchpoint | SelfModify | ModeSwitch | ExternalStop | Fault
```

No engine may return an untyped status integer that callers interpret differently.

### 4.3 Machine graph

`MachineGraph` statically composes:

- harts/cores;
- memory regions and aliases;
- register blocks and devices;
- buses/interconnects;
- clocks and resets;
- IRQ sources/controllers;
- DMA initiators and protected regions;
- PCIe/NVMe endpoint;
- NAND controller/channels/ways/LUNs/planes;
- power, thermal, and fault domains;
- debug/trace and test access infrastructure.

A board is a generated composition, not a large runtime switch:

```simple
val board = MachineGraph.elaborate(BoardProfile.CosmosPlus8Ch8Way)
```

Unknown or incomplete profiles are rejected before execution.

### 4.4 Fast memory and MMIO path

Use a two-level direct map:

```text
virtual/physical address
        │
        ▼
small TLB / page descriptor cache
        │
  ┌─────┴────────────────┐
  ▼                      ▼
RAM/ROM descriptor       MMIO/device descriptor
host-base + offset       generated device + register ID
  │                      │
direct host load/store   SfrBus dispatch + event/effect
```

Required properties:

- RAM accesses do not scan a region list or invoke AOP callbacks.
- MMIO pages force a TB exit or use a safe helper path.
- cross-page, unaligned, endian, atomic, privilege, PMP/PMA, and fault behavior is explicit;
- executable writes invalidate all overlapping TBs and instruction-cache state;
- DMA writes invalidate translated code only when they target executable regions;
- unmapped accesses fault according to the machine profile, never silently return a generic value unless the hardware profile explicitly declares that behavior.

---

## 5. Fidelity ladder: fastest to silicon

### 5.1 Mode definitions

| Level | Mode | Executed code | CPU model | Device model | Timing | Primary claim |
|---:|---|---|---|---|---|---|
| F0 | Algorithm/unit native | canonical algorithm modules, possibly below SFR boundary | native host | direct typed semantic service | none | local algorithm correctness only; **not full firmware parity** |
| F1 | Native SFR behavioral | full canonical firmware source closure compiled for x86/AArch64/RV64 | native host | generated SFR behavioral models | functional events | fastest full-firmware behavioral correctness |
| F2 | Native timed behavioral | same as F1 | native host | SFR + DMA/IRQ/PCIe/NAND event models | virtual device time | concurrency, timeout, ordering, and media scheduling |
| F3 | ISA reference interpreter | exact RISC-V firmware ELF | architectural interpreter | same machine/device contracts | instruction-count time | ISA decode/semantics reference and bootstrap |
| F4 | ISA DBT fast | exact RISC-V firmware ELF | IR_TC TB translation to host | same machine/device contracts | instruction-count/event deadlines | high-throughput architectural validation |
| F5 | ISA timing | exact RISC-V firmware ELF | DBT/interpreter + pipeline/cache/interconnect overlay | timed devices | deterministic approximate cycles | microarchitecture and system timing estimates |
| F6 | Hybrid RTL | exact RISC-V firmware ELF | fast CPU or RTL CPU; selected devices RTL | mixed transaction/RTL | deterministic | focused cycle-accurate regions with fast surroundings |
| F7 | Full RTL | exact RISC-V firmware ELF | Simple RISC-V RTL | RTL SoC/peripherals or verified transactors | cycle/delta accurate | RTL functional correctness |
| F8 | FPGA/HIL | exact RISC-V firmware payload | synthesized Simple RISC-V | FPGA RTL + physical/model media | real FPGA time | implementation, pin, clock, reset, and long-soak evidence |
| F9 | Silicon | exact signed payload with payload hash preserved | manufactured Simple RISC-V/SoC | physical controller/NAND/board | physical time | production qualification |

### 5.2 Relative performance and memory expectations

The table below is a design expectation, not a measured guarantee. CI must replace qualitative values with retained measurements.

| Mode | Speed | Host memory | Startup | Reproducibility potential | Main cost |
|---|---:|---:|---:|---:|---|
| F0 | highest | lowest | lowest | excellent | no platform detail |
| F1 | highest full-fw | low | low | excellent or native-nondeterministic by policy | SFR/device calls |
| F2 | very high | low-medium | low | excellent | event queues and modeled resources |
| F3 | low | low-medium | low | excellent | per-instruction dispatch |
| F4 | high | medium | medium | excellent or host-nondeterministic | decode/IR/native code cache |
| F5 | medium-low | medium-high | medium | excellent | timing state and event volume |
| F6 | low-medium | high | high | excellent | RTL region evaluation/synchronization |
| F7 | lowest software tier | highest | high | excellent | whole-SoC RTL cycles and traces |
| F8 | high wall-clock after build | build-heavy | very high build | high with controlled stimuli | synthesis/place/route/programming |
| F9 | physical | external lab | campaign setup | environmental variation retained | hardware fixtures and destructive tests |

### 5.3 Promotion rule

A feature is not "done" because one fast tier passes. Its evidence grade is the highest level reached:

```text
Behavioral-ready -> ISA-ready -> Timing-characterized -> RTL-verified
-> FPGA-qualified -> Silicon-qualified
```

Documentation and capability manifests must display that grade explicitly.

---

## 6. Scheduling and thread model

### 6.1 Independent scheduling axis

Fidelity does not determine determinism. Define scheduling separately:

| Ordering mode | Host execution | Simulated ordering | Reproducible | Purpose |
|---|---|---|---|---|
| `det_single` | one scheduler thread | canonical total order | yes | simplest reference, debugging, CI |
| `det_parallel` | partitioned host workers | canonical deterministic commit | yes | normal multicore behavioral/timing/RTL acceleration |
| `explore` | one or more workers | seeded or systematically varied legal schedules | yes per seed/path | race, deadlock, starvation, weak-memory exploration |
| `native_parallel` | ordinary host threads | host OS and hardware determine interleaving | no | maximum throughput, sanitizer/race stress, contention/PPA-like software profiling |

### 6.2 Recommended support matrix

| Fidelity | `det_single` | `det_parallel` | `explore` | `native_parallel` |
|---|---:|---:|---:|---:|
| F0 algorithm native | yes | optional | yes | yes |
| F1 native SFR behavioral | yes | **yes** | **yes** | **yes** |
| F2 native timed behavioral | yes | **yes** | yes | yes, non-authoritative |
| F3 ISA interpreter | **yes** | logical SMP only | yes | not useful initially |
| F4 ISA DBT | **yes** | yes | yes | **yes**, one host thread per hart |
| F5 ISA timing | **yes** | **yes** | bounded | optional; never timing authority |
| F6 hybrid RTL | **yes** | **yes internally** | targeted | no semantic benefit |
| F7 full RTL | **yes** | **yes internally** | targeted formal/random | no semantic benefit |
| F8 FPGA | stimulus-controlled | parallel hardware | repeated seeds | physical |
| F9 silicon | campaign-controlled | physical | repeated campaigns | physical |

### 6.3 Canonical event order

Every deterministic event has this key:

```text
EventOrder = (
    virtual_time,
    delta_cycle,
    phase,
    owner_id,
    local_sequence)
```

Suggested phases:

1. external stimulus ingestion;
2. asynchronous reset/power-domain update;
3. combinational evaluation;
4. clock-edge sampling;
5. sequential-state commit;
6. DMA/device completion commit;
7. interrupt line and pending-state update;
8. CPU retirement/trap delivery boundary;
9. observation, assertion, trace, and coverage sampling.

The exact phase table is versioned in the machine profile and result manifest. A change to it invalidates timing/reproducibility baselines.

### 6.4 Deterministic parallel execution

Use conservative partitioned discrete-event simulation with ownership, lookahead, and epoch barriers:

```text
hart0 owner     hart1 owner      PCIe/NVMe owner      NAND ch0 owner
    │               │                  │                    │
 private state   private state      private state        private state
    └──────── timestamped, sequenced messages ────────────┘
                         │
                  deterministic merge
                         │
                    epoch commit
```

Rules:

- one mutable owner for every partition;
- workers mutate only owner-local state during an epoch;
- cross-owner effects are immutable messages;
- messages are merged by `EventOrder`, never arrival time;
- a worker may advance only to its conservative safe horizon;
- device latency provides natural lookahead, particularly NAND program/read/erase and PCIe/DMA transfers;
- zero-delay interactions use delta cycles and terminate under a bounded convergence rule;
- shared-memory writes use a deterministic commit protocol when target memory ordering is modeled;
- optimistic rollback/Time Warp is deferred because state snapshots, anti-messages, and rollback memory would substantially increase complexity and can make firmware debugging harder.

This model permits true host parallelism without making CI results dependent on the host OS scheduler.

### 6.5 Native non-deterministic parallel mode

Map modeled cores and expensive devices onto ordinary host threads:

```text
host thread 0 -> HIL/NVMe hart
host thread 1 -> FTL hart
host thread 2 -> FIL hart
host thread 3 -> background/reliability hart
worker pool   -> NAND physics/ECC or trace compression
```

Use real host atomics, barriers, and rings where they correspond to firmware primitives. This mode finds:

- missing memory barriers;
- lock-free queue defects;
- false sharing and contention;
- starvation under real scheduling;
- accidental global locks;
- host-level races that deterministic ownership might mask.

Its result must include `ordering=native_parallel` and may never satisfy a deterministic release gate by itself.

### 6.6 Schedule exploration

Provide two stages:

1. **Seeded perturbation:** deterministic pseudo-random preemption at declared scheduling points. The seed and selected points are retained.
2. **Bounded systematic exploration:** dynamic partial-order reduction over conflicting effects, with bounds on context switches, event depth, and virtual time.

Scheduling points include:

- ring enqueue/dequeue;
- promise resolve/cancel/timeout;
- lock/atomic/fence;
- SFR read/write with side effects;
- DMA visibility;
- IRQ assertion/acknowledgment;
- metadata commit/checkpoint;
- NAND completion;
- power-fail cutpoint.

The explorer reasons over typed effects rather than arbitrary source lines. This keeps the state space aligned with hardware-visible conflicts.

### 6.7 CPU budgets and event deadlines

The ISA engine executes translation blocks until one of these is reached:

```text
min(normal TB/instruction quantum, next virtual event deadline, debug stop)
```

Fast modes use instruction count only as a scheduling coordinate; they must not claim cycle accuracy. Timing mode maps retired operations, cache/interconnect events, stalls, and device transactions onto modeled cycles.

### 6.8 WFI and polling acceleration

- `WFI` changes a hart to sleeping state and advances it only when an enabled interrupt/debug/reset event can wake it.
- A stable hot loop consisting of MMIO read, mask/test, and backward branch may be recognized as a wait condition.
- The optimizer subscribes the hart to the relevant register/event and skips host execution until that state may change.
- Acceleration is disabled under instruction-by-instruction trace, single-step, or any mode where the skipped instructions are themselves under test.
- A proof/check compares accelerated and unaccelerated observable traces for representative loops.

### 6.9 Snapshot and replay

A machine snapshot contains:

- all architectural hart state;
- memory region versions and dirty pages;
- register/device state;
- pending promises and arena generations;
- event queue and per-owner sequence numbers;
- clock/reset/power state;
- TB cache identity metadata, but not necessarily host code bytes;
- schedule/external-input cursors;
- fault and random-stream state.

Replay logs contain only nondeterministic inputs and selected schedule decisions. They are content-addressed and tied to the exact machine semantic version.

---

## 7. Register, pin, protocol, and effect single sources

### 7.1 RegisterIR

`RegisterIR` is the single source for firmware, emulator, RTL, verification, and documentation views:

```text
RegisterBlock
  id, name, base/size, bus, endian, clock/reset/security domain

Register
  id, offset, width, reset, aliases, array dimensions

Field
  bit range, semantic type, access policy, reserved policy
  write/read side effect, self-clear latency, interrupt relation
  privilege/capability, volatility, atomicity, test visibility
```

Required access policies include:

```text
RO | WO | RW | W1C | W0C | RC | RS | self_clear | shadowed
| pulse | fifo_port | counter | latch_on_event | implementation_defined
```

Generated projections:

- typed Simple firmware accessors;
- native behavioral register bank;
- SimpleEMU MMIO tables and fast dispatch IDs;
- VHDL/SystemVerilog register blocks;
- UVM RAL adapter data;
- SystemRDL/IP-XACT import/export where representable;
- debugger register metadata;
- SSpec field selectors, masks, reset and negative tests;
- human register documentation.

### 7.2 `@reg` source surface

Keep a minimal source annotation model:

```simple
@reg(block=Nfc, offset=0x00, access=wo)
command: NfcCommand

@reg(block=Nfc, offset=0x04, access=rw)
address: NandRowAddress

@reg(block=Nfc, offset=0x08, access=w1c)
interrupt_status: NfcInterruptBits
```

The compiler resolves the attributes into RegisterIR and lowers access into explicit operations:

```text
RegRead<Block, Register, Width, Effect>
RegWrite<Block, Register, Width, Effect>
RegModify<Block, Register, Mask, Effect>
RegFence<BusDomain>
```

Backend behavior:

| Backend | Lowering |
|---|---|
| hardware RISC-V | volatile/ordered MMIO access with required barriers |
| native behavioral | direct generated register-bank call, aggressively inlineable |
| ISA DBT | guest memory operation; RAM/MMIO page map determines dispatch |
| RTL | wires/state/side-effect process generated from RegisterIR |
| formal | uninterpreted/transition relation plus declared invariants |

### 7.3 AOP role

AOP verifies, but does not own, the hot-path semantics.

Immediate implementation with currently available selectors:

- `attr(reg)` marks generated accessors and register declarations;
- `within`/`execution` restrict privileged hardware intrinsics to HAL/register-generator capsules;
- dependency rules forbid firmware imports of emulator/test-control modules;
- compile-time aspects emit access-manifest observations around generated accessors in verification builds.

Compiler work adds first-class effect selectors:

```text
effect(RegRead)
effect(RegWrite)
effect(DmaRead)
effect(DmaWrite)
effect(RaiseIrq)
effect(ScheduleEvent)
effect(NandProgram)
effect(PinDrive)
```

Then policies become declarative:

```text
forbid FTL -> effect(RegWrite<Nfc.*>)
forbid firmware -> effect(TestControl.*)
allow FIL.media_driver -> effect(RegWrite<Nfc.*>)
forbid speculative_path -> effect(RegRead<SideEffecting.*>)
```

Post-link verification checks relocations, imported symbols, access manifests, and section provenance so raw intrinsics cannot bypass the source-level rule.

### 7.4 PinIR and PadIR

Define pins independently from board constraints:

```text
Pad
  logical function, package ball, bank, voltage, direction
  pull, drive, slew, Schmitt, open-drain, differential mate
  clock/reset/power domain, safe reset value, test mode ownership

PinMux
  legal functions, mux SFR, boot strap, conflict rules

BoardConnection
  connector/net, external device, direction, level, constraints
```

Generated views:

- RTL top-level ports and pad-ring wrappers;
- FPGA XDC/SDC/PCF constraints;
- board connection tables;
- BSDL skeleton/input data;
- pin-mux firmware accessors;
- boundary-scan and board-loopback test intent;
- ATE functional pin groups and timing-set input;
- documentation and schematics consistency reports.

### 7.5 ProtocolIR

ProtocolIR supplies typed transactions and shared checkers for:

- PCIe TLP and endpoint events;
- NVMe registers, commands, queue entries, completions, PRP/SGL descriptors;
- AXI/APB/Wishbone operations;
- ONFI/Toggle NAND command/address/data/status cycles;
- JTAG/DMI/IJTAG operations;
- UART, SPI, I2C, GPIO, timers, and interrupt controllers.

A protocol adapter may run at semantic transaction, register, pin, or RTL signal level while emitting the same canonical observation type.

---

## 8. Canonical same-source NVMe firmware

### 8.1 Replace the lane split

The current arrangement contains a broad host firmware and a scalar RV32 re-expression. The target becomes:

```text
canonical firmware modules
     │
     ├─ native host compilation -> F1/F2
     └─ riscv32/64 freestanding compilation -> one ELF -> F3..F9
```

The RV32 scalar implementation remains only as a temporary differential oracle during migration and is then archived. No new feature may be added to it.

### 8.2 Firmware semantic manifest

Every build emits `firmware.semantic.manifest`:

```text
source_revision
compiler_revision
profile_hash
module closure
symbol IDs
normalized HIR hashes
monomorphized MIR hashes
effect summaries
selected providers
layout hashes
register schema hash
async/arena capacity receipt
unsafe/extern inventory
```

Parity gate:

- compare target-independent normalized MIR hashes between native and RISC-V builds;
- explain target-specific differences with a closed allowlist such as ABI lowering, pointer width, volatile access lowering, and startup code;
- reject a function that disappears, gains a mock provider, or changes a safety-relevant branch only on one target.

### 8.3 Build and payload identity

| Tier | Identity requirement |
|---|---|
| F0 | same imported algorithm module hash; may omit platform layers and cannot claim full firmware |
| F1/F2 | same full source closure and semantic manifest; host machine code naturally differs |
| F3-F7 | exact same RISC-V ELF hash |
| F8 | same ELF loaded into FPGA image or same payload segment embedded in image |
| F9 | signed package may differ, but measured firmware payload hash equals F3-F8 |

### 8.4 Configuration without dummy code

A profile is data plus statically selected real providers:

```simple
struct NvmeProductConfig:
    controller: ControllerProfile
    media: MediaProfile
    dram: DramProfile
    cpu: CpuProfile
    queue: QueueProfile
    security: SecurityProfile
    evidence_grade: EvidenceGrade
```

Provider validation is compile-time:

```text
required capability -> exactly one provider -> provider evidence receipt
```

Examples:

- behavioral NFC provider implements the complete declared NFC behavior contract;
- RTL NFC provider binds generated RTL;
- Cosmos+ NFC provider binds real apertures and interrupts;
- an unavailable LDPC provider yields a build error for a profile that requires LDPC.

There is no `DummyEcc`, `NullDma`, `FakeNand`, or `NoopInterrupt` in a certified profile.

### 8.5 Out-of-band test control

Fault injection and state inspection are not methods on production firmware objects. Tests use a separate capability owned by the environment:

```text
TestControlPort
  inject_power_cut
  inject_media_fault
  force_pin
  delay_or_drop_completion
  observe_region_hash
  request_snapshot
```

At F1/F2 it talks to the behavioral environment. At F3-F7 it controls the machine/RTL outside the firmware. At F8/F9 it maps to lab fixtures, debug/test access, controllable power, or reserved destructive media regions. Firmware sees only the physical consequence.

### 8.6 Full embedded async and index-handle requirement

The canonical firmware uses:

- fixed-capacity arenas generated from the product profile;
- opaque generation-checked handles with owner and reset epoch;
- SPSC/MPSC rings selected statically by topology;
- no heap allocation in certified paths;
- explicit state-machine IDs rather than closures;
- promises with shared slot identity, resolve state, waiter list/bitset, deadline, cancellation, and reset generation;
- fail-closed capacity admission before partial side effects;
- deterministic wake ordering in deterministic modes;
- target fences generated from typed ring/memory-domain effects.

The current embedded async module and its skipped test are not sufficient evidence. This runtime is a Wave-2 prerequisite, not a later cleanup.

### 8.7 No-shortcut static gates

Reject production builds containing:

- names or attributes classified as mock/fake/dummy/stub/test-only;
- constant-success providers;
- methods that silently return zero/empty on unsupported hardware;
- direct accesses to emulator media arrays or test-control symbols;
- payload sizes that collapse real data to one byte/word without a profile explicitly labeled teaching-only;
- geometry folding/modulo aliasing;
- host-only branches in safety-relevant code;
- an unverified provider or profile claiming a higher evidence grade.

Each rule ships with positive and negative fixtures and at least one mutation test.

---

## 9. NVMe SSD hardening and missing implementation plan

### 9.1 Required production architecture

```text
PCIe endpoint / NVMe register file
               │
     Admin + I/O queue engine
               │
      PRP/SGL + protected DMA
               │
 HIL async command/task arenas and rings
               │
 FTL mapping/journal/bands/GC/recovery/QoS
               │
 FIL scheduler/ECC/retry/bad-block/media health
               │
 NAND controller channels/ways/LUNs/planes
               │
 real NAND or fidelity-matched model
```

All boundaries use typed messages and index handles. A lower layer never exports its backing arrays.

### 9.2 Missing-part matrix

| Gap | Current floor | Production target | Required evidence |
|---|---|---|---|
| Payload/OOB | compact stand-ins in portions of the model | full page, OOB, metadata, sector/ECC granularity from profile | random full-page round trip, metadata corruption, adjacent preservation |
| Geometry | host constants and physics-model folding/aliasing | channel/way/LUN/plane/block/wordline/page with bijective codec | exhaustive small-geometry proof + large random differential |
| NVMe register transport | modeled command objects and partial AXI floors | CAP/VS/CC/CSTS/AQA/ASQ/ACQ/doorbells, MSI-X, resets, queue memory | register/SFR vectors, Linux/nvme-cli/SPDK differential |
| Host data movement | compact segmented PRP floor | PRP1/PRP2/list, SGL, MDTS, alignment, IOMMU/DMA protection, abort/reset races | descriptor fuzz, DMA trace oracle, fault and boundary matrix |
| Queue concurrency | host loops and partial multi-queue | true async multi-queue, arbitration, backpressure, cancellation, timeout | deterministic schedule exploration + native parallel stress |
| Media parallelism | scheduler exists but is not fully load-bearing | per-channel/way resource occupancy and dependency scheduling | timeline and utilization coverage; conflict/multi-plane/cache ops |
| ECC | stored SECDED floor | pluggable BCH/LDPC/CRC/metadata parity hardware contract; software golden oracle | injected error sweeps, miscorrection prevention, latency/strength profiles |
| NAND interface | behavioral ONFI-like model | real ONFI/Toggle driver, discovery, timing modes, read retry, cache/multi-plane, bad-block rules | pin/transaction vectors and real-chip qualification |
| DRAM | bounded arena/cache floor | controller DRAM initialization, ECC, scrubbing, bandwidth/latency, refresh/error handling | MBIST, ECC injection, bandwidth/timing tests |
| Durability/PLP | modeled crash/replay | persistent superblock/checkpoint/journal layout, capacitor/power-cut timing, torn DMA/NAND operations | named cutpoint campaign across every durable transition |
| Multicore | scalar/cooperative and blocked SMP lane | compiled canonical async firmware on selected Simple RISC-V multicore topology | deterministic parallel, DBT SMP, RTL SMP, FPGA soak |
| Security/update | sandboxed policy floor and modeled firmware admin | secure/measured boot, signed update, rollback protection, debug lifecycle, DMA isolation | negative signature/rollback/debug/DMA campaigns |
| Thermal/power | behavioral values | calibrated sensors, throttling, power states, unsafe shutdown and brownout handling | sensor trace, thermal chamber/model, power fixture evidence |
| Real board/media | postponed/limited FPGA evidence | identified controller board + destructive NAND reservation + lab fixture | immutable campaign pack, independent review, repeated qualification |

### 9.3 Controller and media portability

Keep controller and NAND media profiles independent:

```text
ControllerProfile + MediaProfile + BoardProfile -> validated ProductProfile
```

A product is supported only when all of these exist:

- controller register/interrupt/DMA provider;
- real media driver for the NAND interface/mode;
- geometry and ECC compatibility proof;
- link/clock/reset/pin definition;
- build/package recipe;
- at least the evidence grade advertised by the manifest.

"All controllers" means all controllers for which this complete profile contract has been implemented. It does not mean undocumented proprietary controllers are magically supported.

### 9.4 NVMe behavioral and RTL demonstration topology

Recommended four-hart demonstration:

```text
hart0: PCIe/NVMe/HIL
hart1: FTL mapping/journal/GC coordination
hart2: FIL/ECC/retry/media scheduling
hart3: reliability, recovery, telemetry, background work
```

The exact partition is profile data; a single-hart product uses the same task graph scheduled cooperatively. The emulator can run this topology as deterministic logical tasks, deterministic parallel owners, native host threads, DBT harts, or RTL harts without changing firmware behavior.

### 9.5 Cross-fidelity NVMe observation contract

Every level emits a normalized subset of:

```text
NvmeCommandObserved
NvmeCompletionObserved
QueueDoorbellObserved
DmaTransactionObserved
FtlMappingTransition
JournalCommitTransition
MediaOperationObserved
EccOutcomeObserved
InterruptObserved
PowerTransition
FirmwareTraceEvent
```

Comparators ignore unavailable lower-level detail but never invent it. For example, F1 may expose semantic DMA transactions, F6 pin/RTL detail, and F9 analyzer captures; all must agree on command, data hash, ordering constraints, completion status, and durability outcome.

---

## 10. Simple RISC-V production, debug, trace, optimized-feature, and pin-test plan

### 10.1 Consolidate the processor product

The current project has historical handwritten RTL in `simple-riscv` and richer generated RV32/RV64 cores/debug infrastructure in `simple`. Establish one canonical processor product:

```text
simple-riscv
  source-level hardware modules
  CoreConfig and ISA/UDB capability profile
  generated RTL releases
  debug/trace/DFT/pin infrastructure
  FPGA and silicon evidence

simple
  Simple language, HWIR, elaboration, code generators, SSpec, verification tools
```

Migration rules:

- freeze old implementations under an explicit `legacy` label;
- select one canonical module per architectural function;
- generated RTL is never hand-edited;
- source maps bind every RTL process/net/register to Simple source and HWIR IDs;
- configuration specialization removes unused units at compile time;
- capability documentation is generated from the same manifest consumed by ACT4, Sail, test generation, and synthesis.

### 10.2 Product configurations

At minimum:

| Product | Intended role |
|---|---|
| `rv32_tiny` | minimal embedded/safety/reference core, small debug option |
| `rv32_nvme` | SSD-controller firmware core with atomics, PMP/PMA, debug/trace, ECC/parity |
| `rv64_inorder` | Linux-capable in-order product |
| `rv64_ooo` | performance product with precise commit and speculation controls |
| `rv64_vector` | vector-enabled product |
| `rv64_ooo_vector` | highest-performance compile-time product, not a runtime switch |

Every product has one machine-readable profile and a closed verification matrix.

### 10.3 Production debug module integration

Complete the existing GDB/OpenOCD path against the real hart:

- bind halt/resume/reset/step signals to canonical RV32 and RV64 cores;
- connect abstract GPR/CSR commands to the actual architectural files;
- implement program-buffer execution where required;
- support system-bus access sizes required by tools and target memory;
- support native `stepi`, software and hardware breakpoints;
- implement execution, load/store, address/data, and privilege triggers;
- support per-hart and group halt/resume for multicore products;
- define reset-halt, first-instruction halt, unavailable/nonexistent hart behavior;
- preserve precise debug entry around exceptions, interrupts, WFI, and speculation;
- support authenticated/lifecycle-controlled external debug;
- prevent debug system-bus access from bypassing PMP/security policy in locked production state;
- retain a minimal crash-dump/trace path even when interactive debug is disabled.

The current fake-hart GDB session remains a protocol test, not real-core completion evidence.

### 10.4 Debug and trace security lifecycle

Define lifecycle states such as:

```text
Development -> Provisioning -> ManufacturingTest -> FieldDiagnostic -> Locked
```

For each state declare:

- JTAG/DTM availability;
- authentication keys/challenge flow;
- invasive/non-invasive debug permissions;
- trace permissions and address filtering;
- system-bus access permissions;
- firmware unlock authorization and audit record;
- permanent disable/fuse behavior;
- recovery/RMA policy.

Debug unlock state appears in attestation and retained test evidence. A production-debug feature is not accepted without a security policy.

### 10.5 Architectural and differential verification

Use complementary tools; no one suite is sufficient:

1. ACT4 self-checking ELFs for architectural certification, driven by the exact UDB profile.
2. Sail/Spike/Whisper or another independent ISA model for retirement differential checks.
3. `riscv-dv` constrained-random instruction streams for privilege, exceptions, MMU, debug, and supported extensions.
4. RVFI/riscv-formal for base-ISA and project-specific formal properties.
5. RVVI-style richer retirement/event comparison for asynchronous interrupts, debug, and implementations where net architectural changes are easier to compare than raw pipeline signals.
6. Directed SSpec scenarios for microarchitectural and SoC behavior.
7. FPGA soak and physical board campaigns.

ACT4 is a certification suite, not a complete processor-verification replacement; the release gate requires differential, random, formal, and implementation evidence in addition.

### 10.6 Optimized-feature verification

#### Branch prediction and frontend

Produce directed and random tests for:

- taken/not-taken and alias patterns;
- BTB/RAS capacity and interference;
- compressed 16/32-bit alignment;
- exceptions at fetch/decompress boundaries;
- predictor flush and privilege transitions;
- no wrong-path architectural or MMIO side effects;
- performance counters versus the timing model.

#### Cache, TLB, and memory ordering

Test:

- dirty eviction and latest-data preservation;
- writeback/clean/invalidate operations;
- `FENCE`, `FENCE.I`, aq/rl, AMO, LR/SC;
- self-modifying code and DMA-to-executable memory invalidation;
- PMP/PMA before side effects;
- TLB invalidation, ASID/VMID where applicable, page faults and access faults;
- unaligned accesses and atomicity policy;
- ECC/parity correctable and uncorrectable paths;
- cache/TLB reset and power-domain behavior.

#### Dual-issue/OoO

Test and formally assert:

- monotonic, unique, precise retirement;
- no younger side effect after redirect;
- stores/MMIO only after commit authorization;
- rename/free-list conservation;
- ROB/IQ/LSQ full and replay behavior;
- exception/interrupt/debug precision;
- speculative cacheable loads only after PMA classification;
- deterministic serialize/debug mode matching the in-order architectural trace.

#### Vector/accelerator

Cover masks, tails, `vstart`, fault-only-first, reductions, permutes, memory faults, context save/restore, precise traps, and interaction with debug/interrupts. Generate large datasets and result hashes rather than embedding expected arrays in handwritten tests.

### 10.7 Production observability

Provide a configurable, source-mapped observability fabric:

- retirement trace connector;
- branch/cache/TLB/LSQ/IRQ/debug counters;
- bounded on-chip trace buffers with loss/overflow indication;
- event IDs tied to source and requirement IDs;
- triggerable capture windows;
- last-N-retire crash buffer;
- error syndrome and first-fault registers;
- timestamp source synchronized with device/event traces;
- optional high-speed off-chip trace profile.

Every trace transport reports emitted, captured, dropped, and overflow counts. A prefix cannot masquerade as a complete trace.

### 10.8 Pin, reset, clock, and board testing

Generate tests from PinIR and Clock/ResetIR:

- reset assertion/deassertion ordering and pulse widths;
- every legal pin-mux function;
- GPIO walking-one/walking-zero, high-Z, pulls, open-drain, and interrupt modes;
- input/output loopback where board wiring permits;
- differential pair polarity and lane mapping;
- clock presence, frequency range, switchover, gating, and lock-loss response;
- voltage/power-domain safe states and isolation;
- PCIe reset/reference-clock/link-training observations;
- NAND CE/RB/DQ/DQS/RE/WE/ALE/CLE/WP pin protocol vectors;
- JTAG chain ID, instruction/data register lengths, boundary-scan connectivity;
- UART/JTAG console completeness and overflow;
- package-ball-to-board-net consistency.

The same functional pin vector can drive RTL testbench pins, FPGA board I/O fixtures, and an ATE-functional projection if electrical/timing constraints are supplied.

### 10.9 DFT and manufacturing hooks

Add source-level contracts and generated top-level integration for:

- scan enable/test mode/clock override;
- memory BIST and repair status;
- logic BIST hooks if selected;
- JTAG boundary scan and BSDL generation inputs;
- IEEE 1687/IJTAG-style embedded instrument network and procedures;
- clock/reset test controls;
- analog/mixed-signal observation hooks where applicable;
- fuse/OTP provisioning and readback policy;
- secure manufacturing-test lifecycle.

Important separation:

| Test content | Source |
|---|---|
| Functional boot/protocol/pin scenarios | SSpec TestIntentIR projections |
| Boundary-scan connectivity sequences | PinIR/BSDL + generated/validated sequences |
| MBIST algorithms and expected status | MemoryIR + selected March/test algorithm |
| Scan stuck-at/transition ATPG patterns | external ATPG from scan-inserted netlist |
| Silicon parametric/electrical tests | tester/lab-specific methods, referenced by the common manifest |

SSpec owns intent, campaign orchestration, evidence, and results across these categories; it does not fabricate structural fault coverage.

### 10.10 RISC-V release gates

A production RISC-V product cannot be released until:

- all advertised ISA/profile items resolve to implementation and evidence;
- real-hart GDB/OpenOCD debug tests pass;
- ACT4 plus differential/random/formal campaigns pass;
- required RVFI/RVVI/trace interfaces are non-vacuous;
- optimized-feature mutants are detected;
- pin/reset/clock test packs pass in RTL and FPGA;
- CDC/RDC/reset checks are clean or formally waived;
- ECC/parity injection reaches software-visible recovery;
- synthesis, STA, power, and resource envelopes pass;
- DFT/MBIST/boundary-scan deliverables are generated and validated;
- security lifecycle disables or authenticates invasive debug as specified;
- all evidence is bound to source/RTL/bitstream/tool hashes.

---

## 11. SSpec advanced test-artifact infrastructure

### 11.1 Canonical product: Simple Verification Artifact Pack (SVAP)

Introduce **SVAP v1**, a project-owned, open, versioned test-artifact package. The in-memory model is implemented in Simple; the portable interchange profile uses canonical JSON/JSONL plus content-addressed binary blobs. SDN is an optional native projection.

```text
SVAP/
  manifest.json
  schemas/
  intent/
  target/
  stimulus/
  schedule/
  oracle/
  coverage/
  trace/
  waveform/
  memory/
  projection/
  result/
  blobs/sha256/<digest>
```

The manifest binds every file by SHA-256 and records schema/tool/profile versions.

### 11.2 Typed pipeline

Extend the existing evidence pipeline:

```text
SSpec scenario
  -> TestIntentIR
  -> target-independent ScenarioGraph
  -> target projection / ExecutionPlan
  -> StimulusArtifact + OracleArtifact + CoverageArtifact
  -> runner
  -> RawArtifact + CanonicalTrace
  -> comparator/scoreboard
  -> ComparisonResult + CoverageResult + EvidenceManifest
  -> SVAP result pack
  -> Markdown/manual/dashboard projection
```

Markdown generation is downstream and has no authority to change oracles.

### 11.3 Core records

#### TestIntent

```text
id
requirement_ids
source_span/source_hash
purpose and safety classification
preconditions/resources
parameter/constraint model
stimulus graph
oracle graph
coverage goals
fault and schedule domains
applicable target/fidelity profiles
required evidence grade
```

#### ExecutionPlan

```text
target profile and fidelity
ordering policy
seed and exploration bounds
firmware/image hash
clock/reset/power setup
resource bindings
stimulus projection IDs
oracle/comparator IDs
capture selectors
timeouts and liveness conditions
```

#### Stimulus

Closed typed variants include:

```text
NvmeCommand | PcieTlp | QueueMemoryWrite | DmaAction | AxiTransaction
| SfrAccess | OnfiCycle | NandMediaAction | PinVector | JtagAction
| ClockAction | ResetAction | PowerAction | FaultAction
| DebugAction | MemoryImage | FirmwareImage | HostCommand
```

#### Oracle

```text
Exact | MaskedExact | OrderedSequence | PartialOrder | Eventually
| Never | TemporalWindow | Invariant | Differential | Metamorphic
| NumericTolerance | Distribution | CoverageThreshold | NoDataLoss
| ProtocolConformance | StateTransition | HashEquality
```

Each oracle names selectors, cardinality, timing/order policy, rationale, and requirement IDs. A missing or ambiguous selector fails closed.

#### Schedule

```text
virtual timestamp or named event boundary
delta/phase
owner/source
preemption/fault choice
happens-before constraints
repeat/loop/termination
```

Named event boundaries are preferred for cross-fidelity reuse:

```text
after(NandProgramAccepted) and before(JournalCommitDurable)
```

rather than a hardcoded simulator cycle.

#### Coverage

```text
functional bins and crosses
state/transition coverage
protocol coverage
assertion/property coverage
fault/cutpoint coverage
schedule/interleaving coverage
mutation-kill coverage
ISA normative-rule references
pin/mux/connectivity coverage
```

UCIS import/export can be added as an adapter; SVAP remains the canonical project format.

### 11.4 High-volume trace format

Control metadata remains JSON/SDN. Large streams use a versioned binary envelope:

```text
magic, schema ID, endian, clock/time unit, record type
field dictionary hash, compression, record count, payload hash
```

Initial implementation may use JSONL for clarity. Add a compact binary/zstd profile only after stable schemas and differential tests exist. Never invent a binary format before field semantics stabilize.

### 11.5 Required trace types

- `SfrTrace`: block/register/field ID, operation, value/mask, effect, source, time.
- `BusTrace`: address, width, kind, initiator, response, time.
- `DmaTrace`: descriptor, address region, byte range/hash, protection result.
- `NvmeTrace`: command, queue, state transitions, completion.
- `FtlTrace`: mapping/journal/band/GC/recovery transitions.
- `MediaTrace`: physical address, operation, status, ECC/retry result.
- `IrqTrace`: source, controller state, target hart, claim/complete/ack.
- `RetirementTrace`: RVFI/RVVI-compatible architectural fields.
- `TimingTrace`: pipeline/cache/interconnect/device timing events.
- `PinTrace`: pin group, drive/sample values, masks, timing set.
- `DebugTrace`: DMI/abstract/progbuf/SBA/trigger actions.
- `PowerTrace`: rail/domain/reset/brownout/cutpoint state.
- `CoverageTrace`: observed bins/crosses/transitions.

### 11.6 Target projections

| Projection | Generated content |
|---|---|
| Native behavioral | typed actions, SFR calls, scheduler events, direct comparators |
| ISA interpreter/DBT | ELF/image setup, machine actions, external events, trace selectors |
| Timing | latency profile, event deadlines, timing oracles |
| Native RTL/GHDL/Verilator | clock/reset drivers, bus/pin transactions, assertions, waveform selectors |
| UVM/cocotb | sequence items, drivers, monitor/scoreboard configuration; generated adapter, not canonical source |
| FPGA | host control script/data, JTAG/UART/PCIe transactions, capture instructions |
| Board/silicon | fixture procedure, destructive-region declaration, instrument commands, evidence manifest |
| STIL functional | applicable digital pin vectors, groups, formats, and timing projection |
| SVF/JTAG | boundary-scan/debug shift/update sequences where applicable |
| PSS | optional import/export/mapping after SVAP semantics stabilize |
| UCIS | optional coverage interchange |
| STDF | optional result adapter only; not the canonical internal result model |

### 11.7 SSpec authoring surface

Do not require a new language grammar in phase 1. Add typed library APIs and annotations:

```simple
# @req REQ-NVME-PLP-017
it "recovers a write cut after NAND program and before journal durability":
    var t = test_intent("nvme.plp.program_before_journal")
    t.targets([BehavioralTimed, IsaDbt, HybridRtl, FullRtl, Fpga, SiliconFunctional])
    t.stimulus(nvme_write(qid: 1, lba: Lba(42), blocks: 1, pattern: PatternId("p42")))
    t.schedule(power_cut(after: event("NandProgramAccepted"), before: event("JournalCommitDurable")))
    t.oracle(eventually(nvme_read_after_reboot(Lba(42))).equals(OldOrNewAtomicValue))
    t.oracle(never(event("TornMappingVisible")))
    t.cover(cutpoint("program_to_journal_window"))
    t.capture([NvmeTrace, FtlTrace, MediaTrace, PowerTrace])
    emit_svap(t)
```

After the type model is mature, limited syntax sugar may be added. Ordinary `describe`/`it`/`step`/`expect` remains valid.

### 11.8 Replace temporary capture code

Delete local per-spec helpers such as the current hexdump-based `capture_bit_table`. Replace them with shared providers:

```text
capture_binary_layout
capture_transaction_stream
capture_signal_trace
capture_pin_vectors
capture_memory_image
capture_timing_timeline
capture_coverage
```

These produce typed SVAP artifacts and registered Markdown projections. A capture without an oracle and manifest cannot pass.

### 11.9 One test, multiple implementations

A scenario is projected once per applicable tier:

```text
TestIntent: NVMe queue wrap + abort + power cut
  ├─ F1 native behavioral execution plan
  ├─ F2 deterministic timed plan
  ├─ F4 DBT machine plan
  ├─ F6 NVMe/NFC RTL hybrid plan
  ├─ F7 full SoC RTL plan
  ├─ F8 FPGA host/JTAG plan
  └─ F9 silicon fixture plan
```

The comparator uses common architectural oracles and tier-specific detail oracles. It does not require cycle equality between behavioral and RTL modes.

### 11.10 Functional chip vectors versus ATPG

SVAP can generate and reuse:

- boot/firmware functional sequences;
- bus/register transactions;
- pin drive/sample vectors;
- reset/clock/power procedures;
- boundary-scan connectivity procedures;
- MBIST launch/status procedures;
- software-driven manufacturing diagnostics.

SVAP cannot independently derive high-quality scan ATPG vectors from functional intent. The correct flow is:

```text
scan-inserted netlist + fault models -> ATPG tool -> STIL/pattern artifacts
                                         │
                                         ▼
                                SVAP import + manifest
                                execution + result + coverage
```

This preserves truth while still making SSpec the campaign-level control and evidence system.

### 11.11 Non-vacuity and sabotage

Every generated test pack must prove:

- at least one intended stimulus reached the DUT;
- the DUT, not the harness, produced the observed response;
- required state transitions occurred;
- no capture overflow/truncation occurred;
- timeout cannot be interpreted as pass;
- replacing the DUT result or disabling the relevant path turns the test red;
- a fixture literal cannot satisfy a live capture oracle.

---

## 12. Verification campaigns

### 12.1 Cross-fidelity differential campaign

For each applicable scenario:

1. run F1 deterministic behavioral as the fastest functional baseline;
2. run F1 native-parallel and seeded exploration for concurrency stress;
3. run F4 DBT using the exact release-candidate RISC-V ELF;
4. run F5 timing for selected performance-sensitive scenarios;
5. run F6/F7 RTL for changed hardware, boundary, and release scenarios;
6. run F8/F9 when hardware is available and the scenario is safe/applicable;
7. normalize observations;
8. compare architectural results, partial orders, data hashes, and durability states;
9. retain tier-specific detail and coverage.

Differential authority must be independent where possible:

- ISA results against Sail/Spike/Whisper/ACT expected state;
- NVMe behavior against Linux `nvme-cli`, kernel behavior, SPDK, or another standards-aware host implementation;
- ECC against a separately implemented software model;
- RegisterIR round trips against generated RTL and accessors;
- NAND command behavior against datasheet/ONFI-derived profiles and real-chip captures;
- RTL generation against formal properties and synthesis, not text identity alone.

### 12.2 NVMe command and queue campaign

Generate systematic tests for:

- controller enable/disable/reset transitions;
- admin queue setup and malformed addresses/sizes;
- Identify controller/namespace and capability consistency;
- feature get/set and persistence rules;
- create/delete SQ/CQ dependency rules;
- queue wrap, phase, head/tail, full/empty, arbitration, and fairness;
- multiple namespaces and namespace lifecycle when implemented;
- Read/Write/Flush/DSM/Write Zeroes and selected command sets;
- Abort and races with completion/reset;
- asynchronous events and log retention;
- firmware download/commit/update rollback;
- invalid opcodes, fields, NSIDs, LBA/NLB overflow, and command-ID reuse;
- MSI-X vector mapping, masking, coalescing, and lost-interrupt prevention;
- shutdown notification, abrupt power loss, and controller fatal status.

Artifacts include command streams, queue-memory images, doorbell/SFR traces, DMA traces, completions, and coverage.

### 12.3 DMA/host-memory campaign

- PRP1-only, PRP2 direct, PRP lists, chained lists;
- SGL data block, segment, last-segment and unsupported descriptors;
- page/segment boundary and alignment cases;
- zero/maximum transfer, MDTS, overflow, and malformed loops;
- IOMMU/PMP/protection allow and deny;
- DMA into executable memory and code-cache invalidation;
- concurrent host mutation and device access;
- abort/reset/power loss during DMA;
- completion only after required visibility/fences;
- poisoned/error PCIe completions where modeled.

No host test may read or write private firmware/NAND storage directly to establish success.

### 12.4 FTL and durability campaign

- sequential/random/hot-cold workloads;
- overwrite, trim, flush, and namespace format;
- low-space and GC reserve behavior;
- GC relocation failure at every page;
- journal/checkpoint wrap and torn records;
- mapping-cache dirty eviction;
- recovery from each named durability cutpoint;
- power cut during host DMA, NAND program, metadata program, erase, checkpoint, and superblock switch;
- bad-block discovery and retirement;
- static/dynamic wear leveling;
- read-disturb and retention refresh;
- RAIN/parity reconstruction;
- metadata corruption and version rollback;
- no stale or torn mapping becomes host-visible.

A cutpoint generator derives scenario variants from the durable state machine rather than manually listing only a few crashes.

### 12.5 NAND/ECC campaign

- reset/read ID/parameter discovery;
- read/program/erase/status and ready/busy sequencing;
- cache and multi-plane operations when supported;
- channel/way/LUN interleavings;
- program order/partial-program limits;
- bad-block markers and remapping;
- read-retry/Vref ladder;
- retention, disturb, program/erase failure, and power interruption;
- ECC correction-strength sweep, syndrome errors, metadata/ECC corruption, miscorrection guard;
- full-page and OOB data with independent expected hashes;
- real-chip characterization imports and timing-distribution comparison.

### 12.6 Scheduler and async campaign

- arena exhaustion before side effects;
- promise resolve/cancel/timeout races;
- stale generation and reset epoch;
- ring wrap/full/empty and producer/consumer reset;
- interrupt versus polling completion;
- priority inversion and starvation;
- deterministic-parallel equivalence with deterministic-single;
- seed replay identity;
- native-parallel race stress;
- weak-memory/fence litmus cases on host and RISC-V;
- power/reset while tasks are pending;
- no lost wakeups, duplicate completions, or use-after-free handles.

### 12.7 RISC-V campaign

- ACT4 profile-selected self-checking ELFs;
- random differential instruction streams;
- privilege, CSR, trap, interrupt and delegation;
- MMU/TLB/PMP/PMA and page-table faults;
- atomics and memory-order litmus tests;
- compressed alignment and illegal encodings;
- FP/vector where enabled;
- debug halt/resume/step/triggers/progbuf/SBA/multi-hart;
- branch/cache/OoO directed tests and counters;
- formal core invariants;
- RTL/DBT retirement tandem comparison;
- reset/clock/power and error injection;
- FPGA long-running workloads and watchdog recovery.

### 12.8 Pin, DFT, and manufacturing campaign

- package/board netlist versus PinIR mapping;
- pin mux and boot straps;
- boundary scan chain and connectivity;
- external loopback fixtures;
- JTAG IDCODE/instructions/debug access in allowed lifecycle states;
- MBIST for every memory macro and repair/fail reporting;
- scan/ATPG pattern import and execution status;
- clock/reset test controls;
- power-domain safe-state and isolation;
- provisioning, fuse, and debug lock;
- ATE functional pattern projection where appropriate;
- result/bin mapping and optional STDF export.

### 12.9 Mutation catalog

Mandatory representative mutants include:

- remove one MMIO routing rule;
- return success from an unsupported provider;
- bypass one AOP access rule;
- corrupt one RISC-V decode immediate;
- allow one wrong-path MMIO/store;
- skip one cache dirty writeback;
- remove one interrupt claim/complete;
- duplicate one NVMe completion;
- ignore one DMA bounds check;
- reuse a stale arena generation;
- erase a GC victim before relocation completes;
- omit one journal flush;
- hide one trace/capture overflow;
- swap one package pin;
- disable one MBIST failure indication.

A release gate reports mutation-kill coverage, not merely test count.

---

## 13. Performance, memory, and reproducibility infrastructure

### 13.1 Common benchmark manifest

Each benchmark records:

```text
host CPU/OS/NUMA
compiler and engine versions
source/profile/firmware hashes
fidelity and ordering policy
worker count and partition map
trace/capture configuration
workload and dataset hash
warmup/repetition policy
wall time, CPU time, RSS, allocation, artifact bytes
simulated instructions/cycles/events/transactions
result and reproducibility hashes
```

### 13.2 Mode-specific metrics

| Mode | Primary metrics |
|---|---|
| F1 | commands/s, logical IOPS, host CPU%, allocation count, RSS |
| F2 | events/s, virtual-time advance/s, queue utilization, idle-skip ratio |
| F3 | interpreted instructions/s, dispatch cost, memory-helper cost |
| F4 | guest MIPS, translation time, TB hit/chaining rate, code-cache bytes, invalidations |
| F5 | simulated cycles/s, timing-event volume, cache/predictor model overhead |
| F6/F7 | RTL cycles/s, delta iterations, worker scaling, trace overhead, peak RSS |
| F8 | compile/synthesis/place-route time, resource use, Fmax, host-control throughput |
| F9 | test time/device, retest rate, fixture utilization, data volume, yield/bin statistics |

### 13.3 Reproducibility levels

| Grade | Definition |
|---|---|
| R0 | result only; no replay information |
| R1 | same input/config/seed expected to reproduce pass/fail |
| R2 | canonical architectural trace hash identical |
| R3 | event schedule and trace identity across repeated runs on same engine version |
| R4 | cross-host deterministic identity for architecture/event results |
| R5 | independently reproduced by another engine/tier with equivalent observations |

Deterministic CI targets R4. Cross-fidelity release scenarios target R5 for architectural outcomes.

### 13.4 Baseline and regression policy

- no unmeasured performance promise appears in documentation;
- record median and dispersion across pinned repetitions;
- maintain separate cold-start and steady-state numbers;
- compare like-for-like trace settings;
- fail on statistically significant regressions beyond profile thresholds;
- store compact time series and retain full raw data for flagged runs;
- isolate algorithm, DBT, timing, RTL, and artifact-generation costs;
- add memory-watermark gates to prevent trace/test-data growth from hiding regressions.

### 13.5 Trace-volume control

Support:

- typed filters and trigger windows;
- pre-trigger circular buffers;
- sampling and aggregation only where the oracle permits it;
- compression after canonical record generation;
- per-stream drop counters;
- content-addressed deduplication for memory/images;
- automatic reduced counterexample extraction after failure.

Never drop data silently.

---

## 14. Proposed source layout

### 14.1 `simple`

```text
src/compiler/
  hardware/register_ir/
  hardware/pin_ir/
  hardware/protocol_ir/
  semantics/effect_ir/
  verify/hardware_access/

src/lib/common/emu/
  contracts/
  machine_schema/
  executable_image/
  observation/

src/lib/common/spec/evidence/hardware/
  test_intent/
  svap/
  stimulus/
  oracle/
  schedule/
  coverage/
  projections/

src/app/simpleemu/
src/app/svap/
src/app/spipe_docgen/              # projection only
```

### 14.2 `simple-mllvm-qemu-rtl` / SimpleEMU engine

```text
src/machine/
  graph.spl
  address_space.spl
  region_map.spl
  sfr_bus.spl
  dma_fabric.spl
  irq_fabric.spl
  clock_reset.spl
  power_fault.spl

src/sched/
  virtual_time.spl
  event_queue.spl
  deterministic_single.spl
  deterministic_parallel.spl
  exploration.spl
  native_parallel.spl
  snapshot_replay.spl

src/exec/
  engine.spl
  budget.spl
  exit.spl
  interpreter/
  dbt/
  host/x86_64/
  host/aarch64/
  host/riscv64/

src/device/
  register_device.spl
  uart/
  timer/
  plic_clint/
  pcie/
  nvme/
  axi/
  nand/
  debug/

src/timing/
  cpu/
  cache_tlb/
  interconnect/
  pcie_nvme/
  nand/

src/rtl/
  elaboration/
  native_engine/
  ghdl/
  verilator/
  federated/
```

Keep old imports through compatibility facades until all callers migrate.

### 14.3 `simple-riscv`

```text
src/profile/
src/isa/
src/core/frontend/
src/core/backend/{inorder,ooo}/
src/core/execute/{scalar,fp,vector}/
src/core/memory/
src/core/privilege/
src/debug/
src/trace/
src/soc/
src/pin/
src/dft/
src/verification/
boards/
testpacks/
release/
```

### 14.4 NVMe firmware

```text
examples/09_embedded/simpleos_nvme_fw/
  src/
    profile/
    types/
    runtime/
    hil/
    ftl/
    fil/
    media/
    reliability/
    controller/
    security/
    telemetry/
  boards/
  testpacks/
  proofs/
  release/
  legacy/                 # temporary host/scalar implementations during migration
```

The final product must not retain separate `fw/` and `fw_rv32/` semantic implementations.

---

## 15. Implementation waves

### Wave 0 — Truth reset and freeze

**Goal:** prevent further divergence while defining authoritative ownership.

Tasks:

- pin all four repository revisions and inventory duplicate implementations;
- classify every current emulator, firmware, RTL, board, test, and debug claim by evidence grade;
- freeze `fw_rv32` feature additions;
- label current native RTL as signal/checkpoint model, not complete RTL simulation;
- label current MMIO and async gaps explicitly;
- create red SSpec cases for per-instruction translation, unwired MMIO, silent unmapped I/O, fake capture, skipped async tests, and fake-hart debug limitations;
- publish migration ownership and generated-file rules.

**Exit gate:** no capability claim lacks a path, implementation owner, and evidence class.

### Wave 1 — RegisterIR, PinIR, EffectIR, and SVAP v1

**Goal:** establish single-source hardware semantics and reusable test data before engine expansion.

Tasks:

- implement typed RegisterIR/PinIR/ProtocolIR data models;
- import initial NVMe/NFC, PLIC/CLINT, UART, debug, clock/reset, and pin definitions;
- lower `@reg` attributes into explicit HIR/MIR effects;
- add access-manifest generation and compile-time AOP dependency/attribute rules;
- implement SVAP manifest, intent, stimulus, oracle, schedule, coverage, trace, and result schemas;
- implement content-addressed artifact store;
- replace the local NVMe hexdump capture with a shared provider;
- generate Markdown from SVAP evidence as a projection.

**Exit gate:** one register schema produces firmware accessors, behavioral SFR behavior, RTL skeleton, typed tests, pin/register docs, and a valid SVAP pack.

### Wave 2 — Canonical firmware source and embedded runtime

**Goal:** compile the same NVMe firmware behavior for host and RV32/RV64.

Tasks:

- implement fixed embedded Promise, wake, cancellation, deadline, and reset-epoch semantics;
- implement fixed arenas and opaque generation/owner/epoch handles;
- activate complete async/runtime specs; remove skipped placeholder test;
- migrate HIL/FTL/FIL/controller code to semantic types and fixed storage;
- create static product configuration and provider validation;
- generate semantic manifests for host and RISC-V builds;
- compare normalized MIR closure hashes;
- retire scalar re-expression modules as production paths;
- establish exact firmware payload hash contract.

**Exit gate:** native and RISC-V builds compile from one source closure; all target-independent semantic hashes agree; no dummy/test provider is linked.

### Wave 3 — Native behavioral SimpleEMU

**Goal:** fastest full-firmware execution with real SFR behavior.

Tasks:

- implement MachineGraph, region map, SfrBus, IRQ, DMA, clocks/resets, power/fault control;
- generate behavioral devices from RegisterIR plus explicit state machines;
- wire firmware SFR accesses through generated lowering;
- implement deterministic-single scheduler;
- run full NVMe command/FTL/recovery tests without instruction emulation;
- emit normalized traces and SVAP results;
- validate acceleration against an unaccelerated reference.

**Exit gate:** full canonical firmware passes through SFR/device behavior; no direct service shortcut bypasses the controller path in the full-firmware profile.

### Wave 4 — Parallel deterministic, exploration, and native-parallel scheduling

**Goal:** exercise realistic multicore concurrency without sacrificing reproducibility.

Tasks:

- partition harts, PCIe/NVMe, DMA, FIL, NAND channels, and background work by owner;
- implement deterministic message ordering and epoch commit;
- add conservative lookahead and delta-cycle convergence;
- implement seeded preemption and bounded partial-order exploration;
- implement native host-thread-per-hart mode and worker pools;
- add target memory-order and fence effects;
- compare deterministic-single and deterministic-parallel architectural traces.

**Exit gate:** deterministic-parallel is R4 reproducible across repeated hosts; native-parallel race/throughput results are retained separately.

### Wave 5 — Repair and complete ISA DBT

**Goal:** turn the current per-instruction demonstration into a real multi-ISA DBT engine.

Tasks:

- implement true ELF loading, segments, entry, symbols, permissions, and image digest;
- create TB boundaries and decode multiple instructions per block;
- cache decoded IR and native code;
- key TBs by PC, address-space/MMU context, privilege, ISA mode, endian, and translation semantics;
- implement direct/indirect chaining and safe invalidation;
- wire direct RAM and MMIO helper paths;
- add host backends in order: x86-64 hardening, AArch64, RV64;
- add interpreter as semantic reference;
- add precise interrupt/debug/TB-exit protocol;
- differential-test each ISA against independent references.

**Exit gate:** RISC-V firmware boots/runs by TB execution with no per-instruction IR rebuild; MMIO and self-modifying/DMA code paths are correct.

### Wave 6 — Deterministic timing models

**Goal:** characterize Simple RISC-V and the NVMe platform while preserving reproducibility.

Tasks:

- replace generic instruction count with configurable pipeline model;
- model branch predictor, cache/TLB, store buffer, interconnect, DMA, PCIe/NVMe, DRAM, and NAND resources;
- calibrate parameters against RTL/FPGA measurements;
- emit timing traces and confidence/calibration metadata;
- implement deterministic host-parallel timing evaluation;
- prohibit timing claims from native-nondeterministic mode.

**Exit gate:** retained workloads produce stable timing traces; errors against RTL/FPGA references are measured and within profile-specific acceptance ranges.

### Wave 7 — Production Simple RISC-V debug/trace integration

**Goal:** make the processor debuggable and diagnosable as a real product.

Tasks:

- connect DM/DTM/SBA to real RV32/RV64 harts and memory;
- implement full single-step, triggers, progbuf, required access widths, multicore halt/resume/reset;
- add secure lifecycle/authentication controls;
- add retirement/system trace, PMU, on-chip buffers, crash record, overflow reporting;
- connect source maps and firmware event IDs;
- run GDB/OpenOCD, ACT4, random, differential, and formal campaigns.

**Exit gate:** native GDB step/break/watch/memory/CSR/multihart tests pass on RTL and FPGA; locked lifecycle blocks prohibited access.

### Wave 8 — Native RTL engine

**Goal:** replace signal mirroring with an executable RTL simulation kernel.

Tasks:

- lower Simple HWIR into elaborated nets, processes, memories, instances, clocks/resets;
- implement four-state values where required;
- implement deterministic combinational fixpoint/delta cycles;
- implement edge sampling and sequential commit;
- implement assertions, coverage, VCD/FST-compatible tracing, force/release, and checkpoints;
- support single-clock synchronous subset first, then multiple clock/reset domains;
- use static scheduling and deterministic parallel evaluation groups.

**Exit gate:** generated register blocks, FIFO, DMA fragment, and a small RISC-V pipeline execute natively and match external RTL simulation.

### Wave 9 — Hybrid and external RTL

**Goal:** swap any machine partition between behavioral/timing and RTL implementations.

Tasks:

- define transaction bridge modeled after message/co-emulation boundaries;
- support GHDL and Verilator adapters behind one `RtlBackend` contract;
- allow CPU-fast/device-RTL, CPU-RTL/device-behavioral, and selected-block RTL;
- preserve virtual-time/event ordering and backpressure;
- add state snapshot/restore at safe mode-switch boundaries;
- compare retirement and protocol traces across modes;
- add optional federated simulator adapter after local contracts stabilize.

**Exit gate:** NVMe/NFC or Simple RISC-V can switch to RTL for a selected region without changing the firmware payload or architectural result.

### Wave 10 — Advanced chip/pin/DFT test projections

**Goal:** reuse SSpec intent from logic simulation through manufacturing functional test.

Tasks:

- generate pin vectors and timing-set-neutral groups from PinIR;
- generate GHDL/Verilator/UVM/cocotb/FPGA drivers;
- generate boundary-scan/SVF procedures and BSDL consistency checks;
- generate MBIST launch/status campaigns;
- implement STIL functional-vector projection for eligible digital tests;
- import ATPG patterns and preserve tool/netlist/fault-model provenance;
- add UCIS coverage and optional STDF result adapters;
- add tester/fixture resource and safety metadata.

**Exit gate:** one functional pin scenario runs in RTL and FPGA and produces a structurally equivalent ATE-functional projection; ATPG remains separately sourced and manifest-bound.

### Wave 11 — Real NVMe controller/NAND/board closure

**Goal:** replace remaining modeled silicon boundaries.

Tasks:

- complete PCIe/NVMe endpoint, protected DMA, MSI-X, queues, reset/shutdown;
- complete real ONFI/Toggle media driver and discovery;
- integrate real ECC/DRAM/PLP/power/thermal providers;
- reserve destructive NAND regions and automate board campaigns;
- execute power-cut, endurance, thermal, signal/pin, debug, and recovery campaigns;
- compare real captures with timing/RTL models and recalibrate.

**Exit gate:** identified hardware reaches its declared qualification grade with independent review and immutable SVAP evidence.

### Wave 12 — Release closure

**Goal:** make every claim reproducible, signed, and reviewable.

Tasks:

- sign manifests and release artifacts;
- bind source, compiler, generated RTL, firmware, bitstream, board, and tool identities;
- produce SBOM/license/provenance;
- enforce branch/worktree/review policy;
- run full cross-fidelity release matrix;
- archive raw evidence and reduced failure counterexamples;
- publish generated manuals/dashboard from canonical data.

**Exit gate:** no unresolved P0/P1 issue, no unverifiable claim, no evidence-manifest mismatch, and all required payload/hash parity gates pass.

---

## 16. Parallel workstreams and ownership

| Workstream | Scope | Depends on | Must not own |
|---|---|---|---|
| A — Compiler semantic IR | RegisterIR, PinIR, EffectIR, source maps, backend lowering | none | device behavior |
| B — AOP/access hardening | effect policy, dependency policy, link/binary checks | A | runtime register callbacks |
| C — Machine runtime | MachineGraph, memory/MMIO, devices, IRQ/DMA, snapshot | A | ISA decode |
| D — Scheduling | deterministic, deterministic-parallel, explore, native-parallel | C | device semantics |
| E — ISA/DBT | ELF, decoders, IR_TC TBs, host backends, chaining | C, D | timing policy |
| F — Timing | CPU/cache/interconnect/PCIe/NAND models, calibration | C, D, E | RTL implementation |
| G — Native RTL | HWIR elaboration, event kernel, tracing | A, C, D | firmware algorithms |
| H — External RTL/federation | GHDL, Verilator, bridge, mode switching | C, D, G | canonical RTL semantics |
| I — NVMe firmware | canonical typed async HIL/FTL/FIL/controller/security | A, B | emulation-only controls |
| J — Simple RISC-V | canonical core, optimized features, debug/trace, pins/DFT | A, G | compiler internals |
| K — SSpec/SVAP | test intent, schemas, providers, comparators, projections | A, C | implementation expected values |
| L — Board/silicon | FPGA, NAND fixtures, power/thermal, ATE adapters | H, I, J, K | host-only PASS substitution |
| M — Release/provenance | manifests, signing, evidence archive, review gates | all | implementation shortcuts |

Shared schemas have one owner and version. Consumers propose schema changes through review rather than editing local copies.

### 16.1 Recommended dependency order

```text
A Register/Pin/Effect IR ─┬─> B access hardening
                          ├─> C machine runtime ─> D scheduling ─> E DBT ─> F timing
                          ├─> G native RTL ────────────────┬────> H external/hybrid RTL
                          └─> K SSpec/SVAP ────────────────┘

I canonical NVMe firmware depends on A/B/C/D/K
J canonical RISC-V depends on A/G/K, then H
L hardware qualification depends on H/I/J/K
M release integrates all
```

---

## 17. Acceptance criteria

### 17.1 Firmware parity

- One source closure compiles for native host and RISC-V.
- Normalized target-independent MIR manifests match.
- The scalar RV32 re-expression is not a release implementation.
- F3-F9 firmware payload hashes match.
- No mock/dummy/test-only symbol appears in a production link map.
- Every required capability has exactly one real provider and evidence receipt.
- No unsupported capability silently succeeds or returns inert data.

### 17.2 Register/AOP/hardware access

- Every production SFR is generated from RegisterIR.
- Firmware contains no raw register addresses outside generated/privileged HAL code.
- Native behavioral, DBT, and RTL register semantics pass the same generated tests.
- Direct emulator/NAND/private-array access is rejected.
- Effect and post-link access manifests agree.
- Negative fixtures prove each major access rule fails closed.

### 17.3 Native behavioral emulator

- Full firmware path includes SFR, device state machine, DMA/IRQ, and media service boundaries.
- Full-firmware tests cannot call FTL/media semantic shortcuts directly.
- Deterministic-single runs reproduce R4 traces.
- Deterministic-parallel results match deterministic-single architectural traces.
- Native-parallel is faster or diagnostically valuable and clearly non-authoritative.
- Event/poll acceleration is trace-equivalent to unaccelerated execution.

### 17.4 ISA/DBT

- Real ELF loader validates segments, permissions, entry, and hashes.
- TBs contain multiple guest instructions where legal.
- Hot execution does not rebuild an IR module per instruction.
- Direct RAM and MMIO paths are correct.
- TB invalidation handles CPU writes, DMA writes, and instruction synchronization.
- Interrupt/debug entry is precise.
- RISC-V execution differentially matches an independent model on supported instructions.
- Host x86-64 is stable; AArch64 and RV64 backends have the same conformance suite before being advertised.

### 17.5 Timing and RTL

- Timing model parameters are versioned and calibrated.
- Timing results are deterministic and include error/confidence against references.
- Native RTL evaluates actual combinational/sequential behavior, not checkpoint mirroring.
- Host-parallel RTL preserves logical deterministic ordering.
- Hybrid mode preserves firmware payload and architectural outcome.
- External and native RTL agree on selected modules and traces.

### 17.6 Simple RISC-V

- One canonical hardware implementation per product profile.
- ACT4/UDB capability matrix has no unsupported advertised item.
- Random, differential, and formal campaigns pass in addition to ACT4.
- Real-hart debug supports halt/resume/reset/step/register/memory/triggers and multi-hart policy.
- Trace overflow is detectable and source mapped.
- Optimized-feature mutants are killed.
- Pin/reset/clock/ECC/CDC/RDC tests pass.
- DFT/MBIST/boundary-scan deliverables are present and validated.
- Debug lifecycle/security policy is enforced.

### 17.7 SSpec/SVAP

- SSpec emits a schema-valid machine-readable pack without depending on Markdown.
- Every artifact is hash-bound in the manifest.
- At least one NVMe scenario projects to behavioral, DBT, RTL, and FPGA plans.
- At least one pin scenario projects to RTL, FPGA, and an eligible STIL-functional representation.
- ATPG data is imported from a declared external tool/netlist, not synthesized from a functional guess.
- Captures have typed selectors, independent oracles, and non-vacuity witnesses.
- Failure produces a minimized counterexample pack.
- Markdown can be deleted and regenerated exactly from canonical evidence.

### 17.8 Release

- Full source/compiler/profile/firmware/RTL/bitstream/tool provenance is retained.
- Every advertised evidence grade is met.
- Deterministic release runs reproduce their trace/result hashes.
- Physical results identify board/device/fixture/operator/reviewer and destructive scope.
- No PASS depends only on console text or timeout behavior.
- Critical mutations are all detected.

---

## 18. Risk register

| Risk | Consequence | Mitigation |
|---|---|---|
| "Same source" but divergent monomorphization/providers | native tests do not represent firmware | semantic closure manifests, provider receipts, normalized MIR parity |
| Register AOP placed on hot path | unacceptable firmware/emulator overhead | explicit RegEffect lowering; AOP static/ghost verification; zero-overhead production |
| Deterministic parallel scheduler too complex | delayed delivery or hidden deadlocks | start deterministic-single; conservative epochs; no rollback; trace equivalence gate |
| Native-parallel results misread as deterministic | flaky or false release evidence | explicit ordering grade in manifest; policy forbids release authority |
| Timing model treated as silicon truth | misleading performance claims | calibration metadata, confidence/error, RTL/FPGA comparisons |
| "Native RTL" remains a signal tracker | false RTL completeness | executable process/netlist acceptance tests and external differential |
| Trace volume overwhelms runtime/storage | performance and CI failures | triggers, filters, bounded buffers, drop counters, compression, dedupe |
| Custom SVAP becomes isolated | poor tool reuse | adapters to PSS/UVM/UCIS/STIL/SVF; canonical open schemas; no proprietary dependency |
| Functional vectors mistaken for structural test | escaped silicon defects | explicit ATPG/DFT separation and coverage provenance |
| RISC-V duplicate implementations persist | source and evidence drift | canonical ownership, legacy freeze, generated package interface |
| Debug makes production insecure | invasive access in field | lifecycle/authentication/lock policy, attestation, negative security tests |
| Hardware unavailable | simulated evidence overclaimed | evidence grades, postponed physical gates, no host substitution |
| Compiler throughput blocks full firmware/core | unable to produce exact binary | incremental modules, early compile gates, profile-sized builds, compiler perf workstream |
| Emulator and DUT share same bug | differential tests agree incorrectly | independent Sail/Spike/Linux/host/ECC/real-chip oracles |
| Configuration explosion | untestable product matrix | compile-time product profiles, pairwise/coverage selection, unsupported combos rejected |

---

## 19. Rejected alternatives

### 19.1 Keep host firmware and RV32 scalar firmware separate

Rejected because behavior and fixes inevitably drift, and passing host tests cannot certify the firmware binary.

### 19.2 Put `if simulator` branches in firmware

Rejected because simulation becomes a second implementation inside production code and may bypass the path under test.

### 19.3 Use runtime AOP for every register field access

Rejected because it adds avoidable overhead and makes ordinary field semantics dependent on weaving. Register effects should be compiler IR; AOP verifies the graph.

### 19.4 Make every peripheral a host thread

Rejected because it increases synchronization, memory, nondeterminism, and debugging cost. Most devices are event-driven state machines; workers are reserved for expensive computation.

### 19.5 Make deterministic mode single-thread-only forever

Rejected because owner-partitioned deterministic parallelism can accelerate large device/timing/RTL simulations while preserving canonical commits.

### 19.6 Use optimistic rollback first

Rejected because rollback state and anti-events complicate firmware and device debugging. Conservative scheduling has adequate lookahead in this domain.

### 19.7 Treat instruction count as cycle accuracy

Rejected. Instruction count is a fast scheduling coordinate. Timing requires explicit pipeline/cache/interconnect/device models and calibration.

### 19.8 Use Markdown as the test artifact

Rejected because text manuals cannot reliably drive RTL, FPGA, pins, ATE, replay, or coverage. Markdown is a projection from typed evidence.

### 19.9 Generate ATPG directly from SSpec functional scenarios

Rejected because structural fault patterns require the scan-inserted netlist, fault models, timing, and ATPG algorithms. SSpec/SVAP orchestrates and packages them instead.

### 19.10 Call the current signal tracker a full RTL simulator

Rejected until it elaborates and executes RTL processes/nets with defined scheduling semantics.

---

## 20. Initial implementation slices

### Slice A — Register-to-behavioral-to-RTL vertical slice

Use one small NFC or UART register block:

1. author RegisterIR;
2. generate firmware accessor;
3. generate native behavioral bank;
4. generate RTL block;
5. generate SSpec tests and SVAP register vectors;
6. run behavioral and GHDL/Verilator projections;
7. compare field/reset/side-effect traces;
8. prove raw access rejection.

This validates the central single-source strategy before broad migration.

### Slice B — Same-source one-command NVMe path

Use one real 4 KiB write/read:

```text
NVMe SQ/doorbell -> DMA -> HIL -> FTL -> FIL -> NFC SFR -> NAND model
-> completion/IRQ -> CQ/DMA
```

Compile the exact same modules for native x86 and RV32. Compare normalized observations and semantic manifests. No direct FTL/media shortcut is allowed in the full-firmware profile.

### Slice C — Deterministic scheduling proof

Run the one-command path with:

- deterministic-single;
- deterministic-parallel;
- seeded preemption;
- native-parallel.

Require identical architectural outcome in all modes and identical trace hash in the two deterministic modes.

### Slice D — Real TB execution

Boot a minimal RV32 firmware image through:

- interpreter;
- IR_TC DBT with multi-instruction TBs;
- MMIO UART/NFC;
- interrupt;
- self-modifying/DMA invalidation fixture.

Measure TB cache, chaining, MIPS, RSS, and cold-start translation.

---

## 21. Numbered task backlog (excerpt, as supplied)

> Note: the source text for this section arrived truncated at task 41; tasks 42-90 are
> preserved verbatim below and tasks 1-41 must be reconstructed from Sections 15 and 20
> before this backlog is used for scheduling.

42. Port one FIL operation.
43. Build the same one-command source for x86 and RV32.
44. Compare semantic manifests.
45. Define MachineGraph and profile validation.
46. Implement fast region map.
47. Implement direct RAM path.
48. Implement MMIO slow path.
49. Implement SfrBus generated dispatch.
50. Implement explicit unmapped/fault policy.
51. Implement IRQ fabric and PLIC/CLINT model.
52. Implement DMA region/protection model.
53. Implement virtual-time event queue.
54. Implement deterministic-single scheduler.
55. Implement snapshot/replay base.
56. Execute one-command full path in F1.
57. Emit SFR/DMA/NVMe/media traces.
58. Implement deterministic owner/message model.
59. Implement deterministic-parallel epoch commit.
60. Implement seed-based scheduling perturbation.
61. Implement native-parallel execution.
62. Define target memory-order effects.
63. Implement real ELF loader.
64. Define TB key and boundaries.
65. Decode multi-instruction IR_TC blocks.
66. Cache IR and native code.
67. Implement chain/unchain/invalidations.
68. Bind TB budget to next event.
69. Implement precise interrupt/debug exit.
70. Differential-test RV32 against an independent model.
71. Add AArch64 host backend plan/probes.
72. Implement timing profile and calibration schema.
73. Model pipeline/branch/cache/TLB baseline.
74. Model PCIe/DMA/NAND timing.
75. Integrate real debug module with RV32 hart.
76. Add native GDB step/triggers.
77. Add debug lifecycle controls.
78. Add source-mapped trace/overflow counters.
79. Implement executable native RTL process/net model.
80. Implement delta/edge/commit scheduling.
81. Differential-test register/FIFO blocks against GHDL.
82. Implement Verilator/GHDL common adapter.
83. Implement hybrid transaction bridge.
84. Replace one-byte/folded NAND data with full geometry profile.
85. Add full PRP/SGL protected DMA.
86. Add ECC oracle and hardware provider seam.
87. Generate pin/reset/clock test packs.
88. Add boundary-scan/MBIST/ATPG import adapters.
89. Run one end-to-end FPGA campaign.
90. Produce signed cross-fidelity release evidence.

---

## 22. Standards and external architecture alignment

The project should learn from standards without prematurely claiming conformance.

### 22.1 Emulation and simulation references

- QEMU TCG and instruction-count scheduling: <https://www.qemu.org/docs/master/devel/index-tcg.html>, <https://www.qemu.org/docs/master/devel/tcg-icount.html>, <https://www.qemu.org/docs/master/devel/multi-thread-tcg.html>, <https://www.qemu.org/docs/master/devel/replay.html>
- gem5 CPU models, KVM, and switching/checkpoint patterns: <https://www.gem5.org/documentation/general_docs/cpu_models/>, <https://www.gem5.org/documentation/general_docs/using_kvm/>
- Renode peripheral/register, virtual-time, and co-simulation concepts: <https://renode.readthedocs.io/en/latest/advanced/writing-peripherals.html>, <https://renode.readthedocs.io/en/latest/advanced/time_framework.html>, <https://renode.readthedocs.io/en/latest/advanced/co-simulating-with-an-hdl-simulator.html>
- Verilator multithreaded simulation: <https://verilator.org/guide/latest/verilating.html>
- Accellera SCE-MI/Federated Simulation directions: <https://www.accellera.org/downloads/standards>

### 22.2 Register and portable test references

- SystemRDL 2.0 single-source register descriptions: <https://www.accellera.org/downloads/standards/systemrdl>
- Portable Test and Stimulus 3.0 stable baseline: <https://www.accellera.org/downloads/standards/portable-stimulus>. A PSS 3.1 draft entered public review on 2026-08-31; monitor it, but do not bind a certified implementation to draft semantics.
- UVM, UCIS, IP-XACT, and related standards: <https://www.accellera.org/downloads/standards>
- IEEE STIL 1450-2023: <https://standards.ieee.org/ieee/1450/10488/>
- IEEE STIL.1 1450.1-2025: <https://standards.ieee.org/ieee/1450.1/10489/>
- IEEE JTAG/boundary-scan/IJTAG families should be selected from current active revisions for the product release.

PSS demonstrates the right architectural principle: one scenario intent can target simulation, emulation, FPGA prototyping, and post-silicon. SVAP may support a PSS adapter, but it should first stabilize the project-specific typed observations and hardware data needed by Simple.

### 22.3 RISC-V references

- ACT4 architectural certification tests: <https://github.com/riscv/riscv-arch-test>
- RISC-V Debug Specification: <https://github.com/riscv-non-isa/riscv-debug-spec>
- RISC-V Processor Trace: <https://github.com/riscv-non-isa/riscv-trace-spec>
- `riscv-dv`: <https://github.com/chipsalliance/riscv-dv>
- `riscv-formal`/RVFI: <https://github.com/YosysHQ/riscv-formal>
- OpenHW verification infrastructure: <https://github.com/openhwgroup/core-v-verif>

ACT4 explicitly states that architectural certification tests are not complete verification. The Simple RISC-V gate therefore combines ACT4, independent ISA differential checks, constrained random, formal, directed optimized-feature tests, FPGA soak, and physical qualification.

### 22.4 Semiconductor test-data references

STIL is intended to transfer digital test-vector data between CAE and ATE and carries pattern, format, and timing information. SVAP should use STIL as an export/import target for eligible digital patterns, while retaining its own richer firmware, schedule, provenance, and cross-fidelity records. Structural ATPG remains tool-generated from the scan-inserted netlist.

---

## 23. Definition of done

The emulator/test infrastructure is complete only when all statements below are true:

1. A full NVMe firmware source closure builds natively and for Simple RISC-V without semantic duplication.
2. No certified firmware code contains dummy/mock/no-op behavior or direct emulator-media access.
3. The same RISC-V payload runs from ISA reference through silicon qualification.
4. Register tags generate accessors, behavioral models, RTL, verification metadata, and documentation from one RegisterIR.
5. AOP/effect/link checks prove illegal and direct access cannot enter a certified build.
6. Native behavioral deterministic, deterministic-parallel, exploration, and native-parallel modes exist with explicit result grades.
7. DBT executes cached multi-instruction translation blocks and has correct MMIO, invalidation, interrupt, and debug semantics.
8. Timing mode is deterministic, calibrated, and never confused with instruction count.
9. Native RTL executes real elaborated behavior and agrees with an external RTL engine.
10. Hybrid mode can replace CPU/device partitions with RTL without changing firmware bytes or architectural results.
11. Simple RISC-V supports production-grade debug, trace, optimized-feature verification, pin/reset/clock tests, and DFT hooks.
12. SSpec emits SVAP machine-readable test data; Markdown is fully regenerable.
13. Functional chip/pin vectors are reusable across RTL, FPGA, board, and applicable ATE projections.
14. ATPG, MBIST, boundary scan, and functional tests retain distinct provenance and coverage claims.
15. Every critical gate is non-vacuous, mutation-tested, reproducible, and hash-bound.
16. Physical hardware evidence is never substituted by a host model.

---

## 24. Final recommended sequence

```text
1. Truth reset
2. RegisterIR + PinIR + EffectIR + SVAP
3. Canonical fixed-runtime NVMe firmware
4. Native SFR behavioral deterministic
5. Deterministic parallel + exploration + native parallel
6. Real TB-based DBT
7. Deterministic timing
8. Real-hart debug/trace
9. Executable native RTL
10. GHDL/Verilator hybrid
11. Pin/DFT/manufacturing projections
12. Real controller/NAND/board qualification
13. Signed cross-fidelity release
```

The central architectural rule is simple:

> **One implementation of firmware behavior, one implementation of register semantics, one implementation of processor RTL, and one implementation of test intent—projected into progressively more faithful execution environments.**
