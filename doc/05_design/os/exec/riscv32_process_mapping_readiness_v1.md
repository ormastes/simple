# RISC-V32 process mapping readiness v1

## Landed prerequisite

The bounded shared SysV initial-stack serializer now supports four-byte ELF32
words as well as its unchanged eight-byte ELF64 layout. It rejects unsupported
word widths, every pointer or caller auxv value that would truncate above 32
bits, embedded NULs, overflow, and frames outside the mapped stack. It retains
one materialization per argument/environment string and one exact final-frame
allocation.

`executable_riscv32_mapping_owner_v1.spl` owns the immutable RV32 word size and
can validate copy-only authenticated handle evidence for the exact
`simpleos/riscv32/simpleos` target. The evidence is not authority and mapping
readiness deliberately remains false.

## Remaining safety gates

Canonical dispatch must remain blocked until all of these are connected:

- the RV32 address-space adapter must use an authoritative RV32 paging owner,
  rather than the generic VMM path;
- user mappings and the stack must not overlap Sv32 root entries copied for the
  kernel (the current `0x81000000` stack lies in copied root index 516);
- initial context return must enter U-mode rather than setting `SSTATUS_SPP`;
- authenticated ELF32 layout evidence must be checked before the loader's
  one-shot token is committed/retrieved, not afterward.

Static specs cover four-byte serialization, truncation rejection, exact target
evidence, W+X rejection, and the retained false readiness bit. Per user
instruction, no tests, builds, SPipe, benchmarks, optimizer, or other runtime
verification were run.
