# Internal ELF linker: ELF32 output, i386 relocations, armv7 target (2026-11-16)

Status: verification-pending

## Defect

`SIMPLE_LINKER=internal` (`src/compiler/70.backend/linker/elf/elf_static_link.spl`)
rejected i686 and armv7 at `elf_static_machine` ("slice 1 supports only x86_64
and aarch64"). `RelocArch` had no i386 variant, and the exec writer was
ELF64-only. Since PR #9584, an EM_386 object fails closed in
`reloc_arch_from_machine_checked`.

## Fix

- `reloc_engine.spl`: adds `RelocArch.I386` and the R_386 relocations 32, PC32,
  PLT32 (applied statically), GOT32, GOT32X (unrelaxed), GOTOFF, GOTPC, 16,
  PC16, 8 and PC8. EM_386 now maps to I386. EM_MIPS (8) still fails closed.
- `elf_parser.spl`: i386 SHT_REL implicit addends, read from the field.
- `reloc_scan.spl`: relocation classes for I386 and Arm32. Arm32 used to fall
  through to the AArch64 numbering.
- `elf_exec_writer.spl`: adds `elf_exec_plan_class(..., class32)` and
  `elf_write_image32_bytes`, which write a 52-byte Ehdr with e_flags, a 32-byte
  Phdr and a 40-byte Shdr.
- `elf_static_link.spl`: maps I386 to EM_386 (3) and Arm32 to EM_ARM (40), uses
  4-byte GOT slots, folds the i386 GOT base the way lld does, and copies ARM
  e_flags from the first input.

## Evidence

- Regression spec: `test/01_unit/compiler/backend/linker/reloc_i386_elf32_spec.spl`.
- Freestanding C hello/helper objects for x86_64, i686 (non-PIC and PIC),
  aarch64, riscv64 and armv7 were linked by the internal engine. Each binary ran
  under qemu-user (8.2 static) in WSL Ubuntu-24.04: 3 lines of output and exit
  code 42, the same as ld.lld.

## Remaining gaps (fail closed, not implemented)

1. ELF32 supports static ET_EXEC only. PIE and dynamic links return
   "unsupported ELF32 output mode", because the i386/ARM PLT, GOT dynamic
   relocations and `.rel.dyn` are not implemented.
2. ELF32 output is always stripped, because `elf_append_symtab` writes ELF64
   Sym/Shdr. The fix is to add an Elf32_Sym (16-byte) symtab path.
3. ELF32 bypasses the sealed `layout` / `write_image` operations, which
   validate the ELF64 contract. The operation contract needs a class field.
4. EF_ARM_ABI_FLOAT_HARD (0x400) is not derived from `.ARM.attributes` (lld sets it; input e_flags are EABI5 only). Static binaries run without it. No PT_ARM_EXIDX segment is emitted. `.ARM.exidx` is loaded as ordinary
   read-only data, so unwinding through it is not supported.
5. Parallelism: input parsing, the relocation scan and relocation application
   are all sequential (`elf_static_link.spl:33`). This differs from mold, which
   parses and relocates per file in parallel. A lockless design would have
   per-object workers produce immutable parse and relocation results that a
   single merge step then combines.
6. The internal engine has only been run inside an interpreted/JIT seed
   process. The engine measures 1-8 ms for a link, but the process takes
   ~15 s, almost all of it compiling the linker source. Native wall time and
   RSS have not been measured.
