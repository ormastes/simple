# RV32/RV64 Simple-Generated FPGA CPU and Linux — Research Plan

Date: 2026-07-18
Status: **F1 + N3 selected; design complete; implementation in progress**

This is the detailed implementation plan for the user-selected **F1 + N3**
path. Unchosen options were deleted after selection.

## Non-Negotiable Evidence Rules

1. Authoritative CPU/SoC RTL is compiler output rooted in tracked `.spl` files.
2. Empty architectures, stub/fallback output, copied CPU RTL, emitted-string
   CPUs, and unconditional testbench PASS markers fail the lane.
3. QEMU proves software media and the platform contract, not generated RTL.
4. External cores may be differential oracles only.
5. RV32 and RV64 have independent status and evidence.
6. Simulation, synthesis, ILA, and historical reports do not substitute for a
   board-origin interactive login/`ls` transcript.
7. Missing tools or hardware remain `blocked`/`unsupported`, never skipped PASS.

## Frozen Public and Manual Names

Reuse current public owners and names:

- `RiscvMmuMode`, `RiscvLinuxProfile`, `RiscvPlatformProfile`;
- RV32 `MmuState` and `mmu_*`;
- RV64 `MmuState64` and `mmu64_*`;
- `RiscvFpgaProductProfile` and the current bundle filenames;
- current `check-riscv-*` wrappers, strengthened in place.

Do not add a shared MMU interface until two real call sites demonstrate a
smaller implementation. Use these exact operator-manual step phrases:

1. `Generate RV32 and RV64 RTL from Simple sources`
2. `Exercise Sv32 and Sv39 translation plus PMP protection`
3. `Boot Linux to an interactive login on generated RTL`
4. `Run terminal login and list guest files`
5. `Program each FPGA image and capture board-origin evidence`

Any temporary setup/check helper named by a spec must call `fail(...)` or
`assert(false)` until implemented.

## Milestone 0 — Make Evidence Fail Closed

### Work

- Add a negative gate that rejects an empty CPU architecture, all-constant RVFI,
  missing clock/memory ports, bootstrap/stub fallback, or unconditional PASS.
- Change generated Linux smoke status to `contract` until a DUT-origin retired
  instruction or UART marker is observed.
- Separate `qemu-media`, `rtl-sim`, `synthesis`, and `physical-board` result rows.
- Preserve the existing sidecar field `linuxBootValidated=false` until the
  login/`ls` scenario passes.

### Exit Evidence

- Existing empty RV32/RV64 bundles fail the new gate.
- Wrapper self-tests prove removal of a DUT marker, MMU/PMP witness, Linux
  marker, login prompt, or `ls` output causes nonzero exit.

## Milestone 1 — Compile a Real Simple Hardware Slice

### Work

- Select the smallest existing combinational RV32 and RV64 decode/ALU path as
  internal `@hardware` entries.
- Compile through the canonical VHDL backend, not `generated_*_vhdl()` strings.
- Retain generated source maps and deterministic file hashes.
- Fix only concrete backend gaps surfaced by these entries.
- Replace the empty bundle CPU with a clocked, bus-visible minimal executor that
  retires a short program and drives real RVFI.

### Exit Evidence

- Fresh pure-Simple compiler command emits non-empty VHDL for both lanes.
- GHDL observes PC changes, register writeback, load/store, and a failing illegal
  instruction case from the DUT.
- RVFI/SBY harness binds changing retired-instruction signals.

## Milestone 2 — Privilege, MMU, and PMP

### RV32 Work

- Extend the existing `CoreState` with existing machine/supervisor CSR, trap,
  privilege, and `MmuState` owners.
- Execute CSR read/write/immediate forms, MRET, SRET, SFENCE.VMA, ECALL, and
  delegated exceptions/interrupts.
- Route instruction fetch and LSU accesses through Sv32.
- Preserve 34-bit physical addresses at the page walker/bus boundary.

### RV64 Work

- Connect existing `CoreState64` CSR and privilege state to decoded CSR ops.
- Replace identity `lsu64_access()` with real Sv39 translation.
- Unify the page-table walker with the RV64 memory/bus owner.
- Route instruction fetch and LSU faults through trap entry.

### Shared PMP Work

- Add CPU-owned `pmpcfg`/`pmpaddr` state using the existing PMP plan semantics.
- Implement OFF/TOR/NA4/NAPOT matching, priority, R/W/X, lock behavior, and
  effective-privilege checks.
- Apply translation first, then PMP/PMA checks to the physical access.

### Exit Evidence

- Production functions are called by the executing cores.
- Tests cover Bare, Sv32/Sv39 4 KiB pages, aligned superpages, invalid PTE,
  R/W/X/U/SUM/MXR, A/D policy, page-fault cause/address, TLB hit/miss/refill,
  SATP change, global over-fence, PMP allow/deny/lock, and instruction/data paths.
- GHDL runs one memory-backed program per architecture that observes translated
  data and separate page-fault and PMP-denial traps.

## Milestone 3 — Linux-Capable SoC and Boot Firmware

### Work

- Compile and compose the existing boot ROM, RAM interface, CLINT, PLIC, UART,
  and interconnect from Simple hardware sources.
- Make the DT and hardware map one generated source of truth.
- Implement timer/external interrupt delivery and UART RX/TX.
- Add a Linux-sized memory target: sparse simulation memory and the K26 PL-master
  path to PS DDR for hardware. Do not infer 128 MiB from BRAM.
- Pin OpenSBI and build a deterministic initial `FW_PAYLOAD` image; add
  `FW_JUMP` only after loader/address evidence is stable.
- Pin Linux, DT, and a Buildroot initramfs with serial getty and known fixture
  files for `ls` verification.

### Exit Evidence

- Artifact manifest contains paths, sizes, SHA-256 hashes, tool versions, load
  addresses, and DT memory/peripheral values.
- QEMU RV32 and RV64 boot the exact artifacts to login and `ls`.
- DT audit matches the generated SoC addresses and interrupts.

## Milestone 4 — Generated RTL Linux Login

### Work

- Use a cycle simulator appropriate for full Linux; retain GHDL for focused
  entity tests and use a faster generated-RTL simulator if measured boot time
  requires it.
- Boot the same pinned artifacts on RV32 and RV64 generated RTL.
- Drive UART RX with the login name and `ls /`; capture TX losslessly with a
  bounded timeout and log size.

### Exit Evidence

For each architecture one transcript contains, in order:

- OpenSBI identity;
- `Linux version`;
- DT/init/rootfs markers;
- `login:`;
- accepted shell prompt;
- the transmitted `ls /` command;
- expected root entries and `SIMPLE_RISCV_LINUX_LOGIN_LS_PASS`.

The verifier rejects markers emitted by the testbench rather than UART/DUT.

## Milestone 5 — Compliance and Formal Qualification

### Work

- Create ACT4 UDB profiles matching the actual RV32/RV64 extensions, PMP count,
  misalignment policy, and privileged features.
- Run self-checking architectural ELFs on generated RTL.
- Bind real RVFI to riscv-formal and prove the supported base/extension checks.
- Add bounded MMU/PMP properties: no access on deny, fault cause consistency,
  legal translation stability until fence, and x0 immutability.
- Keep generated Lean/BYL artifacts separate from durable manual constraints.

### Exit Evidence

- ACT4 pass manifest lists every executed ELF and declared exclusion.
- SBY logs contain non-vacuous assertions and covers over changing RVFI.
- `check-riscv-formal-dual-track.shs` and
  `check-riscv-rtl-sby-proof.shs` pass against regenerated real cores.

## Milestone 6 — KV260 Physical Qualification

### Prerequisites

- Resolve the supported Vivado installation without relying on stale PATH state.
- Provide a bidirectional PL terminal: attach a 3.3 V PMOD UART adapter or prove
  a PS/PL RX/TX bridge. Current Xilinx FTDI PS UART and output-only ILA are not
  sufficient by themselves.
- Build a PL-master DDR path and include it in the design/DT.

### Work

- Generate, synthesize, implement, DRC, time, and bitgen RV32 and RV64 separately.
- Program the same connected KV260 sequentially with each bitstream.
- Boot the exact artifact hashes accepted in Milestones 3–4.
- Capture one cold boot and one warm reset through the board-origin terminal.

### Exit Evidence

- Board USB/JTAG identity, FPGA part, compiler/RTL/artifact/bitstream hashes.
- Zero DRC errors and non-negative worst timing slack.
- Resource utilization and achieved frequency, with no optimized-away CPU/RAM.
- Programming transcript and bidirectional Linux login/`ls` transcript for RV32.
- Equivalent independent evidence for RV64.

## Milestone 7 — Qualify and Document Simple as an FPGA Language

### Work

- Publish a user guide from `.spl` hardware boundary through compile, source map,
  simulation, formal, synthesis, bitstream, programming, and live terminal.
- Include supported/unsupported hardware constructs and fail-closed diagnostics.
- Generate the mirrored SPipe manual and review it without opening the spec.
- Refresh architecture/design/tracking/report artifacts and remove stale done marks.

### Final Gate

The feature is complete only when all five frozen manual steps pass for both
architectures, the physical board rows pass, and a highest-capability review
confirms the generated manuals and done marks. Until then the goal remains active.

## Iteration and Verification Budget

- Run each acceptance gate once after the relevant implementation converges.
- At most three fix/verify cycles per milestone.
- Do not rerun an unchanged green gate.
- Prefer focused compiler/entity/MMU/PMP tests before Linux or FPGA gates.
