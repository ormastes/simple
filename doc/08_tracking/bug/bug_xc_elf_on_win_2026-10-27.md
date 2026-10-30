# BUG-XC-ELF-ON-WIN: i686-unknown-linux-gnu objects are emitted as COFF on a Windows host

- Status: open
- Found: 2026-10-27 (cross-compile matrix lane)
- Spec: i686_cross_spec.spl (Linux obj/ar rows)

Evidence binary: C:/dev/p3new/stage2.exe copied to C:/dev/xc/simple_xc.exe (phase-3 stage2, 2026-10-27), Windows 11 x86_64 host, clang/lld 23 (C:/msys64/clang64) + llvm-mingw 20260922 UCRT. Matrix: doc/03_plan/compiler/cross_compile_matrix_plan.md.

## Symptom
`native-build lib.spl --target i686-unknown-linux-gnu --emit-object` -> llvm-readobj `Format: COFF-i386`, `IMAGE_FILE_MACHINE_I386`. Expected `elf32-i386`/EM_386. riscv targets do get ELF, so the object format follows the host OS for x86 triples.

## Cause / location
Object-format/triple selection for x86 targets in the LLVM backend target-machine setup uses the host OS when the arch is x86-family.

## Fix direction
Derive object format from the requested triple's OS component only.
