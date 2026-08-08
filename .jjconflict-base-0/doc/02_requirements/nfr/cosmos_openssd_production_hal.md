# Cosmos+ OpenSSD Production HAL NFRs

## Safety and Determinism

- **NFR-001 - Bounded execution.** Every UART, GIC/SMP, PL310, NFC, PCIe, NAND,
  and boot-state wait shall have a finite limit and return a distinct
  `COSMOS_TIMEOUT` or error. Tests shall exercise both completion and timeout.
- **NFR-002 - Fail closed.** QEMU, an unbound silicon build, an unknown
  bitstream, missing `PCFG_DONE`, malformed MMIO state, or an absent tool/input
  shall not access optional PL registers and shall not emit a production PASS.
- **NFR-003 - Fault containment.** VBAR and dedicated abort stacks shall be
  active before optional MMIO. An abort shall record kind, syndrome, fault
  address, and PC, emit a bounded diagnostic when UART is available, and halt
  without continuing initialization or issuing storage writes.
- **NFR-004 - Data integrity.** NFC DMA buffers shall be aligned, non-overlapping,
  identity-mapped, uncached, reserved from allocators, and held after timeout.
  Board read/program/erase, ECC, PCIe DMA, queue, reset, and power-loss tests
  shall report zero silent data mismatches.
- **NFR-005 - Coherency.** SCU and `ACTLR.SMP` shall precede cache enablement;
  CPU1 shall initialize per-core MMU/L1/GIC state before ACK. Board stress shall
  show no stale shared-memory reads, duplicate/lost interrupts, or DMA
  coherency failures.
- **NFR-006 - Freestanding ABI.** The ARM image shall link with no unresolved
  symbols, host libc, heap, dynamic loader, or exception unwinder. Runtime
  arithmetic shall cover zero, extrema, signed overflow convention, quotient,
  and remainder behavior.

## Build, Evidence, and Operations

- **NFR-007 - Artifact integrity.** Firmware and FSBL shall be ELF32,
  little-endian ARM `ET_EXEC` files with nonzero entry and at least one
  `PT_LOAD`. The bitstream and firmware build contract shall be bound by exact
  identity and SHA-256, and Bootgen output shall be parseable as Zynq boot and
  partition metadata.
- **NFR-008 - Reproducibility.** Evidence shall record repository revision,
  dirty state, tool versions, board serial/revision, boot mode, power fixture,
  commands, environment, timestamps, exit codes, and SHA-256 for all artifacts.
- **NFR-009 - Observability.** Every boot lane shall emit exactly one status from
  `OK`, `UNAVAILABLE`, `INVALID`, `TIMEOUT`, or `HW_ERROR`; the terminal verdict
  shall distinguish QEMU software acceptance from silicon acceptance.
- **NFR-010 - Traceability.** Every REQ/NFR shall map to a host check, board
  procedure, or both. Missing evidence shall be marked `PENDING` or `BLOCKED`,
  never silently omitted or converted to PASS.
- **NFR-011 - Production endurance.** The release board campaign shall include
  repeated cold/warm boot, reset, sustained mixed queue IO, thermal observation,
  NAND ECC-margin/scrub behavior, and controlled power interruption. Exact
  iteration counts and duration shall be recorded before execution and may not
  be shortened after failures.
- **NFR-012 - Claim discipline.** Compilation, QEMU, static source guards,
  synthetic ELF/bitstream fixtures, and fake Bootgen validate software checks
  only. Physical success requires retained evidence from the identified board.
- **NFR-013 - Target isolation and extension.** Adding a board shall add a
  profile and evidence adapter without forking the NVMe command, FTL, or
  recovery core. A target's unavailable capability shall remain explicit, and
  evidence from one target shall not satisfy another target's hardware gate.

## Current Claim and Notes

Scoped H1 runner results cover runtime ABI, PCIe IRQ `61` level-high handling,
controller command/completion and host-DMA FIFOs, bounded IO callback core,
corrected bridge/admin behavior, SMP/cache W^X contracts, QEMU boot, and
packaging self-test. Corrective evidence covers admin Abort/queue/SMART fields,
zero-write-only completion retry, non-retryable post-start completion, and PRP
edges. Those results do not satisfy physical persistence, full end-to-end
board durability, approved FSBL/real package, or H2 evidence. The persistent
NFC/media composition, startup binding, tag validation, and transactional ECC
refresh relocation have host/ARM evidence. The PCIe IRQ covers
configuration/link/error state only, not command arrival; CPU0 targeting is
local policy and board-unproven. The current strict run passed Stage 2/3 but
failed provenance after tracked documentation changed; focused Stage 4 then
segfaulted in `HirLowering.lower_trait` during HIR import resolution. There is
no current pure-Simple runner for final SSpec/doc generation.

Current status: **BLOCKED/FAIL for production acceptance**. REQ-012 and
NFR-011 remain board-only and excluded from passing executable `@req` claims.
Package manifest v3 software provenance now passes its positive and tamper
self-tests. Current Stage-4 SSpec/docgen evidence and physical board proof
remain required.
