# RISC-V32 hosted Linux contract selects an ELF64 sysroot

**Status:** Open; hosted RISC-V32 remains unsupported  
**Component:** compiler/backend target and linker contracts  
**Found:** 2026-07-15

## Problem

`riscv_linux_target_contract(CodegenTarget.Riscv32)` declares an RV32
`riscv32-unknown-linux-gnu` / `ilp32d` target but selects
`riscv64-linux-gnu-ld`, `/usr/riscv64-linux-gnu`, and
`/usr/lib/riscv64-linux-gnu`. The repository's available GNU cross sysroot
contains ELF64 CRT objects and has no RV32 multilib, so those files cannot
provide a correct hosted RV32 link.

The LLVM support matrix already marks RISC-V32 unsupported and bare-metal-only.
Platform defaults must not invent `/usr/riscv32-linux-gnu` paths until a real
ILP32D libc/sysroot/toolchain contract is selected and verified.

## Required resolution

Choose and verify one hosted RV32 GNU or musl sysroot, then make the target
contract, CRT discovery, dynamic loader, GCC triplet, and toolchain probe use
that same owner. Until then, supported RV32 builds use the tested
`riscv32-unknown-none-elf` bare-metal contract with empty sysroot/CRT paths.
