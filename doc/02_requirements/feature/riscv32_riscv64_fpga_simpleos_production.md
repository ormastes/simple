<!-- codex-research -->
# RV32/RV64 Simple-Generated FPGA CPU and Linux — Feature Requirements

Status: **Selected — F1 compiler-first modular integration**

Selection date: 2026-07-18. The user selected **F1**. These requirements keep
the existing Simple RV32/RV64 modules and close concrete compiler/backend and
integration gaps in executable slices. An imported, handwritten, copied, or
string-emitted CPU may be a diagnostic oracle only; it cannot satisfy a
requirement below.

## In scope

- Existing RV32 `CoreState`/`MmuState` and RV64 `CoreState64`/`MmuState64`
  modules, CSR/trap logic, SoC profiles, RVFI, VHDL backend, Linux media flow,
  and K26/KV260 integration.
- Small compiler-supported `@hardware`/`@clocked` boundaries added to the
  existing module owners, followed by composition of emitted entities.
- Independent RV32 and RV64 results. Evidence from one architecture never
  substitutes for the other.

## Functional requirements

### REQ-001 — Canonical Simple-to-RTL production path

The canonical RV32 and RV64 CPU/SoC entities shall be emitted by the Simple
compiler from tracked `.spl` hardware roots. The build shall name the source
root, compiler identity, source map, generated RTL hash, and unsupported-
construct diagnostics. Empty architectures, constant-only cores, fallback or
stub lowering, emitted VHDL strings, copied RTL, and external CPU RTL shall fail
the production gate.

### REQ-002 — RV32 Linux-capable execution profile

The RV32 product shall implement an explicitly reported
RV32IMAC_Zicsr_Zifencei profile with M/S/U privilege, traps/interrupts, the
required CSRs, atomics, and a real fetch/load/store path. Optional extensions
shall be enabled only when their architectural tests pass. The production path
shall execute the boot media, not a marker-specific instruction subset.

### REQ-003 — RV32 Sv32 and PMP integration

Instruction fetch and load/store shall call the production `MmuState`/`mmu_*`
Sv32 implementation, with SATP mode/ASID/PPN handling, SFENCE.VMA invalidation,
permission checks including U/S behavior, superpages, page-fault causes, and
A/D-bit policy. CPU-visible PMP CSRs and TOR/NA4/NAPOT enforcement shall run
after translation and before any bus side effect. Locked entries shall obey the
privileged architecture contract.

### REQ-004 — RV64 Linux-capable execution profile

The RV64 product shall implement an explicitly reported
RV64IMAC_Zicsr_Zifencei profile with M/S/U privilege, traps/interrupts, required
CSRs, atomics, and real fetch/load/store execution. `core64_update`, CSR access,
and exception delegation shall be connected to the emitted state machine; the
production path shall not use the current PC-increment or identity-LSU stubs.

### REQ-005 — RV64 Sv39 and PMP integration

Instruction fetch and load/store shall call production `MmuState64`/`mmu64_*`
Sv39 translation. SATP writes, SFENCE.VMA, TLB invalidation, three-level walks,
superpages, permission checks, A/D policy, canonical-address faults, and precise
page/access-fault causes shall be executable. PMP requirements are identical to
REQ-003 and independently tested on RV64.

### REQ-006 — Linux-capable SoC and terminal

Each architecture shall expose a documented Linux platform with executable
reset vector, RAM/DDR, CLINT-compatible timer/software interrupts,
PLIC-compatible external interrupts, and a bidirectional UART or equivalent
terminal. Address maps, interrupt IDs, clock frequency, memory size, and boot
arguments shall be emitted into a matching device tree. The terminal shall
accept login input and shell commands; TX-only markers do not satisfy this
requirement.

### REQ-007 — Pinned software-media oracle and generated-RTL boot

Each architecture shall build pinned OpenSBI/firmware, Linux, device-tree, and
Buildroot/rootfs artifacts. QEMU shall validate the software/platform media as a
separate oracle row. Generated RTL simulation shall boot the same artifact
hashes to `login:`, accept credentials, reach a shell, execute `ls /`, and
retain DUT-origin logs. QEMU success shall never be reported as RTL success.

### REQ-008 — Architectural and formal qualification

Each declared ISA/privilege profile shall pass focused production-module tests,
ACT4 architectural tests, and non-vacuous RVFI/SymbiYosys properties. Formal
gates shall prove reset/progress and bounded instruction/exception properties
against the real emitted entity and shall fail on missing assertions, constant
RVFI, unavailable DUTs, timeouts, or missing solver/tool output.

### REQ-009 — Independent physical FPGA qualification

The connected KV260 shall be programmed independently with RV32 and RV64
bitstreams produced from the canonical generated RTL. Each lane shall retain
board/part identity, implementation reports, bitstream/programming hashes, and
a board-origin cold-boot and warm-reset transcript that reaches login and runs
`ls /`. Simulation logs, ILA-only markers, or an external CPU bitstream cannot
substitute for interactive board evidence.

### REQ-010 — Reproducible guide and evidence contract

A detailed guide and mirrored SPipe manual shall cover hardware source,
compiler diagnostics/source maps, generated RTL, simulation, architecture and
formal tests, synthesis/implementation, bitstream programming, and interactive
terminal proof. Every gate shall report `pass`, `fail`, or `blocked` with exact
artifact provenance; unavailable evidence shall never become a pass. Broad
findings, exclusions, generated-manual quality, and done marks require final
normal/highest-capability review.

## Delivery order

1. Remove false-green RTL/Linux evidence and establish compiler provenance.
2. Emit and execute honest RV32 and RV64 slices from existing Simple modules.
3. Integrate Sv32/Sv39 and PMP into fetch/load/store.
4. Close ISA, privilege, interrupt, and formal gaps.
5. Boot pinned media in QEMU and generated RTL.
6. Add DDR/bidirectional terminal and qualify RV32 then RV64 on KV260.

## Out of scope

- A second RISC-V core, bootloader, FPGA framework, or speculative shared MMU
  abstraction.
- External CPU RTL as product implementation.
- N4 multi-board/ASIC qualification; it is a separate follow-on goal.
