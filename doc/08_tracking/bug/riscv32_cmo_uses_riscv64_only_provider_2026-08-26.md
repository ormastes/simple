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

## Verification evidence (2026-11-05)

Already fixed by `eb763ab5295` ("fix(riscv32): use XLEN-sized native CMO
leaves", merged to `release/1.0.0` via PR #6416). Verified on worktree
`work/libbug-linux-rv32cmo-20261105` at `adfeae3765c`:

- `src/os/kernel/arch/riscv32/cmo.spl` provides all eight CMO leaves as pure
  Simple inline asm with XLEN-sized `u32` operands; zero `extern fn`, zero
  `rt_riscv64_*` references.
- `src/os/kernel/arch/riscv32/hal_cache.spl:8` imports
  `os.kernel.arch.riscv32.cmo.{...}` — not the shared
  `std.nogc_async_mut_noalloc.baremetal.riscv` lib whose `rt_riscv64_*`
  SFFI providers exist only in the riscv64 freestanding runtime.
- Repo-wide grep: the shared `baremetal.riscv.cmo` lib is imported only by
  riscv64 kernel code and tests; no RV32 consumer remains.
- Regression spec `test/01_unit/os/riscv32_cmo_provider_spec.spl` (added by
  the fix) locks both invariants; PASS under the seed interpreter binary:
  `outcome=OK declared>=2 executed=2 passed=2 failed=0`.

Residual: native RV32 object/hardware evidence for the inline-asm leaves is
still pending a target run (this host is aarch64); interpreter execution skips
inline assembly per the leaf comments.
