# Simple linker: `.ARM.exidx` / PT_ARM_EXIDX not emitted for armv7

- **Status:** open
- **Found:** 2026-11-18, while triaging armv7 static glibc (#10258)
- **Area:** `src/compiler/70.backend/linker/elf/elf_static_link.spl`, `elf_exec_writer.spl`

## Symptom

For the same armv7 static glibc hello inputs, ld.lld 18 emits `.ARM.exidx`
(SHT_ARM_EXIDX, 0x860 bytes, SHF_LINK_ORDER) and a `PT_ARM_EXIDX` (0x70000001)
program header covering it. The Simple linker emits neither: `llvm-readelf -lS`
on `hello_libc_static_slk` shows no EXIDX segment and no `.ARM.exidx` section.

The hello program runs anyway, because nothing on its path unwinds. Anything
that unwinds with the ARM EHABI will fail: C++ exceptions, `_Unwind_Backtrace`,
glibc `backtrace()`, and `pthread_cancel` cleanup through libgcc_s/libunwind.
The unwinder finds the table through `__exidx_start` / `__exidx_end` (static)
or `dl_iterate_phdr` + PT_ARM_EXIDX. Neither symbol is defined, and the
segment is missing.

## Needed (matching ld.lld)

1. Collect the input `.ARM.exidx*` sections (SHT_ARM_EXIDX = 0x70000001) into
   one output `.ARM.exidx`. Order the entries by the address of the code
   section each one links to (`sh_link`, SHF_LINK_ORDER), and keep them when
   their linked text section is kept (GC).
2. Apply R_ARM_PREL31 to each entry. Insert the EXIDX_CANTUNWIND terminator
   sentinel (lld's `ARMExidxSyntheticSection`). Optionally merge duplicate
   CANTUNWIND entries.
3. Define `__exidx_start` / `__exidx_end`.
4. Emit a `PT_ARM_EXIDX` program header over the section.
5. Spec: a two-function armv7 object with `-funwind-tables`. Check the
   section, the sorted PREL31 entries, the symbols and the PT_ARM_EXIDX
   phdr. Run-check: a static C++ throw/catch or `_Unwind_Backtrace` under
   qemu-arm.

## Evidence

- `llvm-readelf -lW hello_libc_static_lld`: `EXIDX 0x000194 0x00010194 ... 0x00860 0x00860 R 0x4`
- `llvm-readelf -SW hello_libc_static_lld`: `[ 2] .ARM.exidx ARM_EXIDX 00010194 000194 000860 00 AL 6 0 4`
- The Simple output has no `ARM_EXIDX` section and no EXIDX phdr.
