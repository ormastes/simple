# RISC-V Gen2 Atomic Extension: Local Research

Date: 2026-08-12
Status: requirement selection pending

## Question

What is the smallest honest Gen2 A-extension product boundary that can replace
the legacy atomic paths without claiming atomicity from ordinary LSU traffic?

## Current assets

- `src/lib/hardware/riscv_common/isa/scalar_database.spl` has no A/Zaamo/Zalrsc
  rows, so strict Gen2 dispatch rejects every atomic instruction.
- Gen2 already has typed scalar completion, trap, retirement, LSU request/
  response ownership, protocol-fault aggregation, and explicit FENCE effects.
- Legacy RV32/RV64 code contains AMO arithmetic and reservation state, but it is
  core-specific, not a typed Gen2 provider, and cannot establish a shared-bus
  atomicity guarantee.
- `RiscvRetireRecord` already permits simultaneous read/write masks for an AMO.

## Gap

An ordinary load followed by an ordinary store is not an AMO. Gen2 needs a
typed atomic transaction authority, reservation invalidation input, aq/rl
ordering effects, exact instruction identity, and one held completion before A
can be advertised.

## Decision boundary

Do not reuse legacy core state or represent AMOs as two independent LSU
requests. Select one of the feature and NFR options before implementation.
