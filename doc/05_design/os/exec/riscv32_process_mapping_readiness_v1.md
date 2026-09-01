# RISC-V32 process mapping readiness v1

## Landed prerequisite

The bounded shared SysV initial-stack serializer now supports four-byte ELF32
words as well as its unchanged eight-byte ELF64 layout. It rejects unsupported
word widths, every pointer or caller auxv value that would truncate above 32
bits, embedded NULs, overflow, and frames outside the mapped stack. It retains
one materialization per argument/environment string and one exact final-frame
allocation.

`executable_riscv32_mapping_owner_v1.spl` owns the immutable RV32 word size and
validates copy-only authenticated handle evidence for the exact
`simpleos/riscv32/simpleos` target. The admitted user half is now strictly below
`0x80000000`, disjoint from the copied Sv32 kernel-root half.

An isolated authoritative mapper was drafted and rejected during static safety
review. It was removed rather than retaining an unenforceable ownership claim.
The required registry/lease boundary and rollback quarantine are recorded in
the blocker below.

## Remaining safety gates

Canonical dispatch must remain blocked until all of these are connected:

- the RV32 stack policy/default selector now names `0x7ffff000`, below the
  copied kernel half, but the canonical ELF process-image builder still rejects
  RV32 and always requests an eight-byte stack; it must admit RV32 and select
  the existing four-byte serializer before the future mapper binds the value;
- an opaque registry-backed mapper must bind a live loader joint lease, own the
  root and frames, and quarantine any PTE whose unmap fails before freeing;
- the scheduler must consume/move that owner and perform the one-shot SATP plus
  U-mode entry transfer; mapping receipts never authorize execution;
- the authenticated loader joint transition must call the mapper before token
  commit/retrieval and bind its result to scheduler adoption.

Static specs cover four-byte serialization, truncation rejection, exact target
evidence, W+X rejection, and the retained false readiness bit. Per user
instruction, no tests, builds, SPipe, benchmarks, optimizer, or other runtime
verification were run.
