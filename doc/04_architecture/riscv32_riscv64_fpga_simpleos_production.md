<!-- codex-design -->
# RV32/RV64 Simple-Generated FPGA CPU and Linux Architecture

Date: 2026-07-18
Status: selected architecture for F1 + N3

## Decision

Use compiler-first modular integration. Keep the existing RV32 and RV64
behavioral module owners, introduce the smallest synthesizable boundaries they
need, and make the canonical Simple VHDL backend the only producer of product
CPU/SoC RTL. Build upward in executable slices; evidence remains fail-closed
until a slice is real.

This document extends the existing RISC-V architecture documents. It replaces
their readiness assumptions where they conflict with current source evidence;
it does not create another RISC-V stack.

## Architectural invariants

1. Product RTL flows `.spl hardware root -> Simple compiler -> HWIR/VHDL ->
   simulator/synthesis`. No string emitter, copied CPU RTL, Rust-seed fallback,
   or external CPU may cross that boundary.
2. RV32 and RV64 are sibling capsules. They share only public next-layer
   contracts; neither reads the other's private state or helpers.
3. Every instruction/data access follows `virtual address -> MMU -> physical
   address -> PMP/PMA -> bus`. A fault stops the request before a bus side
   effect.
4. QEMU, RTL simulation, formal, synthesis, and board execution are separate
   evidence planes. Status never promotes across planes.
5. Generated artifacts are immutable evidence identified by their source,
   compiler, tool, and content hashes.

## Layered structure

<!-- sdn-diagram:id=riscv32_riscv64_fpga_simpleos_production.architecture -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv32_riscv64_fpga_simpleos_production.architecture hash=sha256:auto render=ascii
@layout dag
@direction LR

Public_profiles -> RV32_core_capsule
Public_profiles -> RV64_core_capsule
RV32_core_capsule -> RV32_hardware_boundary
RV64_core_capsule -> RV64_hardware_boundary
RV32_hardware_boundary -> Simple_VHDL_backend
RV64_hardware_boundary -> Simple_VHDL_backend
Simple_VHDL_backend -> Generated_SoC
Generated_SoC -> Focused_GHDL_ACT4
Generated_SoC -> RVFI_SymbiYosys
Generated_SoC -> Linux_RTL_simulation
Generated_SoC -> KV260_implementation
Pinned_Linux_media -> QEMU_media_oracle
Pinned_Linux_media -> Linux_RTL_simulation
Pinned_Linux_media -> KV260_implementation
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv32_riscv64_fpga_simpleos_production.architecture hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

### Layer 1 — Public platform contracts

Owner: `hardware.riscv_common.pkg.riscv_linux_pkg` and existing profile modules.

Public types remain `RiscvMmuMode`, `RiscvLinuxProfile`,
`RiscvPlatformProfile`, and `RiscvFpgaProductProfile`. They describe XLEN, ABI,
MMU mode, address map, firmware handoff, and evidence state. They contain no CPU
state, page-table walker, FPGA resource, or cached artifact.

### Layer 2 — Architecture-specific CPU capsules

Owners:

- RV32: `hardware.rv32i_rtl` and its existing CSR/trap/MMU submodules.
- RV64: `hardware.rv64gc_rtl` and its existing CSR/trap/MMU submodules.

Each capsule owns register file, PC/pipeline state, privilege, CSRs, trap state,
TLB, page walker, and XLEN-specific PMP state. Only typed ports, RVFI, and
profile/status values leave the capsule. Internal flat TLB layouts and walker
states remain tree-private.

Instruction-width adaptation is also capsule-private. RV64C expands into the
existing RV64 base decoder, but original 2/4-byte length and fault parcel remain
clocked core state so PC, link, trap, and semihost behavior cannot be inferred
from the expanded instruction.

The two capsules deliberately retain `MmuState`/`mmu_*` and
`MmuState64`/`mmu64_*`. A shared MMU abstraction is prohibited until two real
compiled call sites reveal a smaller common interface.

### Layer 3 — Compiler hardware boundary

Owner: existing Simple hardware annotation/lowering and VHDL backend modules.

The hardware boundary is an adapter over the real module owner, never an
alternate CPU. Combinational helpers may use `@hardware`; state transitions use
the supported clocked/process boundary. Compiler diagnostics must name the
unsupported source construct and location. Fallback or partial emission is a
typed failure.

Generated VHDL and source maps are outputs, not hand-edited inputs. The bundle
orchestrator may package them but may not synthesize CPU semantics with string
templates.

### Layer 4 — Generated SoC composition

Owner: existing `hardware.soc_rtl` and RISC-V FPGA/Linux composition modules.

The SoC composes emitted CPU, boot ROM, external-memory interface, CLINT, PLIC,
UART, and interconnect. One typed platform description supplies both address
decode and device-tree values. Focused simulation can use sparse memory; KV260
uses a PL-master path to Linux-sized PS DDR. BRAM-only memory is diagnostic and
cannot satisfy Linux or board acceptance.

### Layer 5 — Artifact and evidence orchestration

Owner: `hardware.fpga_linux.riscv_fpga_linux`, current `check-riscv-*`
wrappers, SPipe acceptance, and reports.

This layer packages immutable artifacts and evaluates evidence. It does not
implement instructions, MMU/PMP, UART responses, Linux markers, or formal
properties. Its state machine is:

`contract-not-ready -> rtl-generated -> architecture-validated ->
rtl-linux-validated -> fpga-validated`

Promotion requires all earlier evidence for the same XLEN and identical
artifact hashes. `fail` and `blocked` remain first-class results.

## CPU memory-access architecture

For each fetch/load/store:

1. Decode access kind, size, effective privilege, SUM/MXR, and virtual address.
2. In M-mode/Bare, form the architectural identity result; otherwise issue the
   existing Sv32/Sv39 walker/TLB operation.
3. On translation fault, write the precise cause/address and enter the existing
   trap path. Do not issue a bus request.
4. Run the physical address through the XLEN-local PMP priority matcher.
5. On PMP denial, raise an instruction/load/store access fault before any bus
   request.
6. Only an allowed physical request reaches the SoC interconnect.
7. Commit state and RVFI only when the architectural event is valid.

Page-table walker memory accesses are themselves physical accesses and must be
subject to the privilege architecture's PMP rules. SATP changes and SFENCE.VMA
invalidate the appropriate TLB entries; a safe global flush is accepted before
address/ASID-selective fencing is optimized.

## PMP ownership

The current bare-metal `PmpRegion`/`PmpCsrWrite` module remains the software
programming-plan owner. CPU RTL adds XLEN-local state and match/check functions
inside each core capsule because synthesizable width/layout differs. Shared
constants may move to `hardware.riscv_common` only after both consumers exist.

Required semantics are ordered entry priority, OFF/TOR/NA4/NAPOT address
matching, R/W/X validation, lock behavior, effective privilege, and default
allow/deny rules from the pinned privileged specification.

## Linux and terminal architecture

Pinned media consists of firmware/OpenSBI, kernel, DT, and rootfs with a serial
getty and deterministic fixture files. A manifest binds their hashes, load
addresses, entrypoints, DT values, and tool identities.

QEMU validates only that media and platform contract. RTL and FPGA lanes must
observe bytes originating at the DUT UART and must send login and `ls /` bytes
back through the same proved RX/TX transport. Wrapper- or testbench-injected
success markers are invalid.

On KV260, JTAG programs one architecture at a time. A proved PS/PL serial bridge
or attached 3.3 V PMOD UART supplies bidirectional terminal evidence. ILA may
diagnose internal progress but cannot satisfy interactive acceptance.

## Formal and compliance architecture

- ACT4 profiles declare only implemented extensions and platform properties.
- RVFI is driven from the same commit path as architectural state, never a
  constant or formal-only shadow core.
- SymbiYosys harnesses contain named assertions and cover points bound to the
  emitted DUT. Missing assertions, no changing RVFI, missing solver output, or
  timeout is failure/blocker evidence.
- MMU/PMP properties prove no bus access after a denied/faulting request, cause
  consistency, stable permitted translation until invalidation, and x0
  immutability.

## Error model

Compiler and orchestration errors are structured statuses with lane, phase,
source/artifact, reason, command, and log path. Key reasons include
`unsupported-hardware-construct`, `stub-or-fallback-output`,
`empty-or-constant-core`, `artifact-hash-mismatch`, `dut-marker-missing`,
`formal-proof-vacuous`, `terminal-not-bidirectional`, and
`physical-board-unavailable`.

An unavailable external prerequisite may be `blocked`; semantic mismatch is
`fail`. Neither is converted to pass or skip.

## Architectural decisions

### ADR-1 — Keep sibling RV32/RV64 cores

Accepted. It reuses implemented state and avoids a speculative parameterized
core while the two implementations remain asymmetric.

### ADR-2 — VHDL backend is canonical

Accepted. HWIR-first whole-core redesign and external-CPU-first integration are
rejected for this goal because they delay or weaken proof of Simple-generated
product RTL.

### ADR-3 — Evidence hardening precedes positive RTL claims

Accepted. Existing empty cores and unconditional PASS testbenches must become
explicitly non-ready before a real slice replaces them.

### ADR-4 — External DDR and bidirectional terminal are board requirements

Accepted. Linux-sized BRAM and output-only markers cannot qualify the physical
product.

## Dependency and change boundaries

- Source/core changes stay in their existing architecture capsule.
- Compiler changes are limited to concrete gaps exposed by selected hardware
  entries and receive focused backend regression tests.
- Orchestration imports only public profile/artifact/evidence contracts.
- Generated artifacts never become sources of truth.
- Unrelated active-session work is excluded from this lane.

## Completion boundary

The architecture is qualified only when both lanes independently reach
`fpga-validated`, all REQ/NFR evidence is current, and the primary reviewer
accepts the generated manual and done marks. Intermediate milestones remain
useful but do not complete the user goal.
