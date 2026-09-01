# Pure Simple ARM32 emit-object contract

This unit contract protects the ARM32 bare-metal target policy and the exact
Cosmos relocatable-object acceptance runner.

The policy keeps an explicit `eabihf` request in the LLVM target triple while
leaving short or soft-float ARM aliases on conservative `eabi`. The runner
requires a hash-bound admitted Pure Simple compiler and checks the real CLI path, ELF32/ET_REL/ARM
header, hard-float attributes, exported C symbol, consumer relocation,
`ld.lld -r` consumption, and absence of `__aeabi_unwind_cpp_pr0`.

Execution evidence is intentionally not claimed by this manual.
