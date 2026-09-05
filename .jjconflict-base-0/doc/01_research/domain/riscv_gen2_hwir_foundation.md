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

## Independent compressed truth provenance (2026-08-12)

The upstream Sail RISC-V model exposes compressed decoding through the
`encdec_compressed` mapping and defines Zca instructions in
`model/extensions/C/zca_insts.sail`. For mission-critical evidence, merely
copying those mapping formulas into a Simple test would destroy implementation
independence. The admitted workflow instead acquires an exact upstream commit,
verifies source digests, and requires an external batch adapter to enumerate
every 16-bit parcel separately for RV32 and RV64.

The fixture contract records classification, canonical expansion when one
exists, original length, and semantic name for all 65,536 parcels. Content and
generator SHA-256 values are mandatory. The evidence remains fail-closed when
the adapter or truth tables are unavailable, and an oracle fixture is never by
itself a product qualification receipt.

Source: [Sail RISC-V tag 0.10](https://github.com/riscv/sail-riscv/tree/a33475aeb80090127433b5a8b30e717edaa19e71),
[pinned Zca semantic mapping](https://github.com/riscv/sail-riscv/blob/a33475aeb80090127433b5a8b30e717edaa19e71/model/extensions/C/zca_insts.sail).
