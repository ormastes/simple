# RISC-V Gen2 HWIR Foundation — Domain Research

Date: 2026-08-11

Multi-level hardware IR practice separates structural hardware, combinational
logic, sequential state, target legalization, debug and verification so that
optimization and source lineage precede HDL serialization. CIRCT documents
separate hardware, combinational, sequential, handshake, debug and verification
dialects, supporting this separation without requiring Simple to adopt CIRCT.

RISC-V products need elaboration-time specialization: RV32 and RV64 are
separate concrete netlists while sharing semantic tables and provider contracts.
RVC/Zc further requires exact original parcel/length preservation through
retirement; that work depends on the first typed configuration and strict
lowering boundary, but is not implemented here.

Sources: [CIRCT dialects](https://circt.llvm.org/docs/Dialects/),
[RISC-V compressed extension](https://docs.riscv.org/reference/isa/v20260120/unpriv/c-st-ext.html).

## Decision

Start with a fail-closed, deterministic semantic slice rather than an empty
entity. It establishes the contracts that subsequent typed registers, memories,
channels, aspects, ISA entries, parcel fetch, optimization, and target profiles
will extend.
