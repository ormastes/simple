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
2. Closed (2026-11-16, verification-pending): ELF32 output now carries
   `.symtab`/`.strtab` (`elf_append_symtab32`, 16-byte Elf32_Sym, 40-byte
   Shdr) unless stripped. For i686, the hello link's `llvm-readelf -s` output
   matches ld.lld's 7 entries.
3. ELF32 bypasses the sealed `layout` / `write_image` operations, which
   validate the ELF64 contract. The operation contract needs a class field.
4. Partly closed (2026-11-16, verification-pending): armv7 e_flags now include
   EF_ARM_ABI_FLOAT_HARD (0x400) when an input's `.ARM.attributes` has
   Tag_ABI_VFP_args = 1, and EF_ARM_ABI_FLOAT_SOFT (0x200) otherwise, as
   ld.lld does (0x5000400 / 0x5000200). Still open: no PT_ARM_EXIDX segment is
   emitted, and `.ARM.exidx` is loaded as ordinary read-only data, so
   unwinding through it is not supported.
5. Partly closed (2026-11-16, verification-pending): the relocation scan and
   apply (non-RISC-V) now fan out over per-object ranges on lockless workers
   (`elf/elf_par.spl`, CAS gate + immutable snapshot, flat `[i64]` results
   merged in order). Output is byte-identical to jobs=1 on all six hello
   targets and on a 200-object / 120k-reloc set. Still open: parsing stays
   serial (an `ElfObject` cannot cross a thread, see
   `isolated_thread_args_drop_arrays_structs_2026-11-16.md`), and the fan-out
   is a net LOSS today. On the 200-object set, jobs=16 takes 42.0 s against
   30.3 s for jobs=1, because the snapshot copies and the `[i64]` encoding
   cost more than the scan and apply save. Serial phases dominate.
6. Measured natively (2026-11-16, Windows x86_64 native build of a driver;
   lld/mold run in WSL on the same objects):

   | set | internal j1 | internal j16 | ld.lld | mold |
   |---|---|---|---|---|
   | hello (2 objs, per arch) | 1-2 ms engine | 2-3 ms | 20-30 ms, 56 MB | 10 ms, 7 MB |
   | 200 objs, 120k relocs, x86_64 | 30.3 s, 10.0 GB HWM | 42.0 s, 10.0 GB | 0.12 s, 68 MB | 0.10 s, 7 MB |

   Internal numbers are engine time inside one process; HWM is the process
   peak. The internal linker is about 250x slower than lld at scale, and its
   memory use is pathological (about 1.2 GB per MB of input). Its output runs
   correctly (qemu rc=0).
