# RV32 cache maintenance imports RV64-only SFFI providers

- **Status:** OPEN; UNSAFE-TAGGED
- **Filed:** 2026-08-26
- **Area:** RISC-V bare-metal cache maintenance
- **Severity:** high — an exercised RV32 cache path can lack its declared target
  implementation

## Evidence

The shared Pure Simple owner
`src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl` declares eight symbols
named `rt_riscv64_*`. Both RV64 and RV32 HAL cache modules import its public
wrappers, but the concrete instruction providers exist only in
`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`. No RV32 provider was
found for those identities.

The declarations and calls are now explicitly `unsafe(ffi)`, so source no
longer presents the unresolved target ABI as verified-safe. This tagging does
not make the RV32 path functional or admitted.

## Required resolution

Keep cache policy and range iteration in Pure Simple. Split only the target
instruction leaf by architecture, using exact XLEN-sized operands, or add an
RV32 freestanding provider with a distinct, correctly named ABI. Gate Zicbom,
Zicboz, and Zicbop instructions on admitted capability evidence and bind the
exact provider bytes, compiler, ABI registry, and firmware/hardware evidence.

Do not add generic dispatch, symbol lookup, allocation, or per-call signature
verification to the cache-line loop. Admission belongs at load/boot time and
the hot path must remain one cached/direct instruction leaf per line.
