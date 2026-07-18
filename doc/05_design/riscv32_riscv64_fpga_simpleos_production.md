<!-- codex-design -->
# RV32/RV64 Simple-Generated FPGA CPU and Linux Detail Design

Date: 2026-07-18
Status: implementation design for selected F1 + N3

## Design goals

- Replace false-green generated RTL evidence with a real compiler-produced
  execution path, one convergent slice at a time.
- Integrate the existing Sv32/Sv39 and CSR/trap owners instead of duplicating
  them.
- Add CPU-enforced PMP for both XLENs.
- Reuse one pinned Linux media set per architecture across QEMU, RTL, and KV260
  while retaining separate evidence rows.

No TUI or GUI design is required. The user-facing surface is a command-line
operator flow and generated SPipe manual.

<!-- sdn-diagram:id=riscv32_riscv64_fpga_simpleos_production.design -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv32_riscv64_fpga_simpleos_production.design hash=sha256:auto render=ascii
@layout dag
@direction LR

Tracked_Simple_core -> VHDL_compile_source_map
VHDL_compile_source_map -> GHDL_program_RVFI
GHDL_program_RVFI -> MMU_translation
MMU_translation -> PMP_check
PMP_check -> SoC_bus
Pinned_media -> QEMU_oracle
Pinned_media -> Generated_RTL_login
Generated_RTL_login -> Bidirectional_login_ls
Bidirectional_login_ls -> KV260_RV32
Bidirectional_login_ls -> KV260_RV64
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv32_riscv64_fpga_simpleos_production.design hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Frozen names and manual flow

Public types remain `RiscvMmuMode`, `RiscvLinuxProfile`,
`RiscvPlatformProfile`, RV32 `MmuState`/`mmu_*`, RV64
`MmuState64`/`mmu64_*`, and `RiscvFpgaProductProfile`.

The primary manual contains exactly these visible steps:

1. `Generate RV32 and RV64 RTL from Simple sources`
2. `Exercise Sv32 and Sv39 translation plus PMP protection`
3. `Boot Linux to an interactive login on generated RTL`
4. `Run terminal login and list guest files`
5. `Program each FPGA image and capture board-origin evidence`

## Milestone 0 — Fail-closed evidence

### Bundle behavior

Until a real compiled core is present, the current generated filenames remain
available as a contract bundle but carry status `contract-not-ready` and reason
`placeholder-core-no-semantic-rvfi`. Diagnostic entities shall terminate with
`GENERATED_RTL_NOT_IMPLEMENTED lane=<rv32|rv64>` when executed.

Generated testbenches shall not emit PASS, Linux, DTB, MMU, login, or completion
markers. Formal harnesses shall be visibly non-ready and cannot produce proof
success. Existing future marker names may remain metadata only.

### Wrapper behavior

The existing dual-arch wrapper continues aggregating both lanes. Missing tools
or self-hosted runtime return the documented tool/blocker status; diagnostic
RTL returns nonzero. A successful exit is permitted only after the runner sees
DUT-origin evidence and the expected lane marker.

### Focused tests

- Generated core contains the diagnostic and lacks a fake executable pass.
- Sidecar reports `contract-not-ready` and `linuxBootValidated=false`.
- Testbench contains no executable `report "... PASS"` statement.
- Runner rejects the diagnostic marker and a removed/missing DUT marker.
- Dual-lane aggregation returns nonzero when either lane fails.

## Milestone 1 — Compiler-produced execution slice

### Hardware entries

Select an existing RV32 decode/ALU path and existing RV64 decode/ALU path that
compile without inventing a second core. Add the smallest internal hardware
entry annotations. The stateful entry then owns clock/reset, instruction/data
bus request/response, and RVFI commit ports and calls the same existing
combinational/update helpers used by software-model tests.

The bundle generator invokes or consumes the canonical compiler output; it
never embeds VHDL source text for CPU semantics. Generated artifacts include
source root, compiler hash/version, source map, VHDL hash, and diagnostics.

### Minimal observable program

The first clocked slice executes a bounded program covering PC sequencing,
integer ALU, register writeback, branch/jump, load, store, and illegal
instruction trap. GHDL checks values observed through DUT ports/RVFI. RVFI
`valid`, `order`, `insn`, `pc_rdata`, `pc_wdata`, register, and memory fields
change consistently with retirement.

## Milestone 2 — RV32 Sv32/PMP

### State changes

Extend existing RV32 core state with current machine/supervisor CSR and trap
owners, privilege, `MmuState`, and an RV32-local `PmpState`. `PmpState` stores
the supported `pmpcfg` bytes and `pmpaddr` values in fixed synthesizable fields.
`PmpCheckResult` returns allowed/denied plus matched entry for evidence.

The first connected RV32 protection slice moves the existing machine CSR and
PMP owners into `CoreState`, routes CPU `pmpcfg*`/`pmpaddr*` operations through
the fixed CSR helper, and calls `pmp32_gate_access` before every Bare-mode
fetch/load/store bus helper. Locked M-mode denials raise causes 1/5/7 with the
faulting address in `mtval` and suppress read/write side effects. S/U privilege
transitions now preserve current privilege through MPP on machine trap entry
and restore it with MRET; MPRV selects MPP for data but never fetch. CSR access
checks privilege, implemented addresses, and read-only write intent before
retirement. `mstatus` is the sole sstatus storage; `medeleg` routes implemented
U/S synchronous exceptions into `sepc/scause/stval` and the S status stack, and
SRET restores U/S state while clearing MPRV. `mideleg`, `sie`, and `sip` remain
WARL-zero until supervisor interrupt delivery is connected. SATP likewise
reads Bare and ignores Sv32 writes until the request/response walker lands; the
RAM-backed translation adapter is not used as production RTL.

### Translation algorithm

- Preserve Sv32's 34-bit physical address at walker and bus boundaries.
- Add ASID state and SUM/MXR inputs; choose a documented A/D update policy.
- Replace direct `RamState` page-table reads in the production path with a
  request/response walker FSM. Unit tests may retain a memory-backed adapter.
- Implement TLB refill, global mapping semantics, and safe global SFENCE.VMA;
  optimize selective invalidation only after correctness is proved.
- Route fetch/load/store through translation, then `pmp_check` before bus issue.

### Fault handling

Invalid/reserved PTEs, misaligned superpages, permission/A/D failures, and
walker access failures enter the existing precise trap path with `*tval` equal
to the virtual address. PMP denial produces the matching access fault.

## Milestone 2 — RV64 Sv39/PMP

Extend `CoreState64` with RV64-local PMP state. Connect decoded CSR operations,
SATP writes, `core64_update`, `mmu64_set_satp`, `sv39_walker64_start/cycle`,
`mmu64_flush`, trap delegation, and SRET/MRET to the emitted state machine.
`core64_cycle` replaces the PC-only step and clocks the canonical memory
frontend through two-parcel fetch, decode/commit, and stalled data access. The
permissive `lsu64_access` identity product path is deleted. The SoC latches one
bus response and routes accepted physical requests exactly once.
The clock path validates encodings before starting data access, samples
CLINT/PLIC pending state into `mip`, and takes enabled interrupts only after an
instruction commits. `misa` grows only when the corresponding execution path is
connected. M is multi-cycle; A uses translated physical reservations and
interrupt-free read/conditional-write phases. Only DRAM accepts atomic-tagged
requests, so ROM/MMIO rejection occurs before target side effects. The reusable
core profile leaves A clear; only `core64_init_single_master()` enables it for
this exclusive-bus SoC.

RV64C is a fail-closed 16-to-32-bit expansion layer feeding the same base
decoder. `CoreState64.instruction_bytes` preserves the original length through
loads, stores, M, and A phases. Sequential PC and control-flow link values use
`pc + instruction_bytes`; JALR clears bit zero; trap EPCs align to two bytes;
illegal compressed instructions report the original parcel. Compressed EBREAK
cannot participate in the 32-bit semihost sequence. The reusable profile is
RV64IMC+S/U and the exclusive-bus SoC profile is RV64IMAC+S/U.

For explicit data accesses, `core64_effective_data_privilege` selects MPP only
when the current mode is M and MPRV is set. Fetch and trap entry always use the
current mode. The selected privilege, SUM, and MXR are latched in the memory
transaction and reused by both AMO phases. The S-mode CSR owner owns the
SIE/SPIE/SPP/SUM/MXR alias; machine CSR reads/writes and trap transitions merge
that view into `mstatus`. SXL/UXL are fixed RV64 fields, MPP=2 coerces to U, and
the current direct-only trap owner clears unsupported vector modes.

Supervisor interrupt state is canonical in the machine CSR file. `sie` exposes
only delegated supervisor enable bits; `sip` permits supervisor software to
write delegated `SSIP`, while machine firmware can inject `SSIP`, `STIP`, and a
software `SEIP` latch. The software `SEIP` latch is ORed with the independent
PLIC S-context line; CSR read/modify/write operates on the hidden software
latch while returning the combined architectural bit. The PLIC provides the
standard context-1 enable, threshold, and claim/complete windows and excludes
an in-service source from both contexts until its owning context completes it.
Delivery checks all machine-target causes before all supervisor-target causes,
orders S causes as external/software/timer, suppresses
delegated interrupts in M-mode, and treats global SIE as implicit below S-mode.

Sv39 rejects noncanonical addresses, supports three-level walks and aligned
1 GiB/2 MiB/4 KiB leaves, applies U/S/SUM/MXR and A/D rules, refills the TLB,
then performs RV64 PMP before bus issue. Fault cause/address and RVFI trap fields
come from the real commit path.

## PMP detailed behavior

For entries in increasing index order:

1. Decode OFF, TOR, NA4, or NAPOT from the config byte.
2. Compute the byte range from the current/previous `pmpaddr` values.
3. Require the complete access range to match one entry; a partial overlap
   fails.
4. Apply R/W/X permissions for the access kind and effective privilege.
5. Honor locked entry write protection and M-mode applicability.
6. Use the first matching entry. Apply the architecture default when none
   matches.

The existing bare-metal `pmp_write_plan` remains a configuration producer; RTL
tests cross-check that its NAPOT plans program equivalent CPU state.

## Linux SoC and media

### Generated platform description

One immutable platform record supplies reset address, RAM/DDR range, CLINT,
PLIC, UART, interrupt IDs, timebase, clock, and console. VHDL interconnect and DT
generation consume the same values; a checker rejects mismatches.

### Memory and peripherals

- Focused simulation: sparse request/response memory with deterministic latency.
- Full RTL simulation: sparse Linux-sized memory initialized from pinned media.
- KV260: AXI PL-master bridge to PS DDR with reset/clock-domain handling and a
  declared usable range.
- UART: real RX/TX FIFOs/status/interrupt behavior sufficient for serial getty.
- CLINT/PLIC: timer, software, and external interrupt behavior required by
  OpenSBI/Linux.

### Artifact manifest

For each XLEN record path, size, SHA-256, load address, entrypoint, tool
identity, configuration hash, and DT relationship for firmware, kernel, DTB,
rootfs, and optional combined image. QEMU, RTL, and FPGA consumers reject a
different hash set.

## Linux execution and evidence

The terminal driver waits in order for OpenSBI, `Linux version`, init/rootfs,
and `login:`. It transmits credentials, waits for a shell prompt, sends `ls /`,
checks deterministic fixture entries, and records
`SIMPLE_RISCV_LINUX_LOGIN_LS_PASS`. The completion marker is written by the
checker only after observed DUT bytes and transmitted command evidence; it is
not present in RTL/testbench source.

Logs have explicit timeouts and size limits and record byte direction. A runner
rejects reordered/synthesized markers, output-only transport, command absence,
wrong artifact hashes, or wrapper-origin prompt text.

## Formal and ACT4 design

- Generate ACT4 UDB profiles from the declared product profile, then compare
  them with the implemented extension/CSR/PMP counts before execution.
- Bind RVFI to the compiler-emitted entity. Calibration fixtures must prove
  missing/changing signals and missing assertions fail.
- Required bounded properties: reset reaches fetch; retired order increases;
  x0 is immutable; trap/no-retire consistency; no bus request on MMU/PMP fault;
  permitted translation stability until SATP/fence; denied PMP writes stay
  ineffective when locked.
- Keep readiness checks separate from strict proof pass.

## KV260 implementation

Build RV32 and RV64 separately from regenerated VHDL and pinned media. The
implementation manifest binds Xilinx part/board identity, constraints, clock,
DDR and terminal paths, synthesis/implementation/DRC/timing/resource reports,
bitstream, and programming log.

After programming, capture cold boot and warm reset through a proved
bidirectional terminal. Preserve raw bytes and decoded transcript. ILA traces
are supporting diagnostics only. Non-negative worst slack and zero DRC errors
are required; initial utilization/frequency values become frozen NFR ceilings
only after both real designs complete.

## Error handling

Every stage returns a structured lane result containing:

- architecture and stage;
- `pass`, `fail`, or `blocked`;
- reason code and human summary;
- command/tool identity and exit status;
- input/output hashes;
- log/evidence paths and timestamps.

Semantic mismatches are `fail`. Missing board/tool/adapter is `blocked`.
Neither is coerced to success. Temporary spec helpers fail explicitly until
implemented.

## System-test structure

Executable acceptance lives at
`test/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.spl`.
Its generated manual mirrors under `doc/06_spec/03_system/...`. The five visible
steps form the operator flow; matrices, negative fixtures, and detailed per-REQ
checks are folded. Each REQ has happy, edge, and fail-closed coverage. Hardware
unavailability is a visible blocker and never an ignored test.

## Verification order and stop criteria

1. Bundle/evidence unit and negative contract tests.
2. Focused VHDL compiler entry tests.
3. RV32 and RV64 MMU/PMP unit/integration tests.
4. GHDL program and RVFI calibration tests.
5. ACT4 and strict formal gates.
6. QEMU media oracle, then generated-RTL Linux.
7. RV32 KV260, then RV64 KV260, each cold and warm.
8. SPipe docgen, guide/doc freshness, and final primary review.

Each converged acceptance gate runs once per session, with at most three
fix/verify cycles per milestone. Passing gates are not repeated.
