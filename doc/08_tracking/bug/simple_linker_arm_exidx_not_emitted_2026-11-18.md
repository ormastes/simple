# Simple linker: `.ARM.exidx` / PT_ARM_EXIDX not emitted for armv7

- **Status:** verification-pending
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

## Fix (2026-11-19, lane ssos)

- **What the static engine (`elf_static_link.spl`, `section_gc.spl`, `elf_exec_writer.spl`) now does:**
  - Merges EM_ARM `.ARM.exidx*` inputs into one output `.ARM.exidx` (0x70000001, flags 0x82, sh_link `.text`).
  - Keeps an exidx input only when its sh_link'd section is live. Exidx is never a GC root.
  - Orders entries by the output text address.
  - Synthesizes CANTUNWIND entries for text that has none.
  - Drops adjacent duplicate inline/CANTUNWIND entries.
  - Ends the table with a CANTUNWIND sentinel at the end of `.text`.
  - Emits PT_ARM_EXIDX (ELF32 only).
  - Defines `__exidx_start` and `__exidx_end`.
  - Stops treating R_ARM_NONE personality references as undefined.
- **Comparison with lld:** `.ARM.exidx` bytes, segments, all alloc sections and the unwind table are identical to ld.lld for the `exidx_{a,b}` fixture and the arm32 SimpleOS hello. In the hello, .text is now at 0x401148, the same as lld.
- **Specs:** `elf_arm_exidx_spec` 4/4 and `simpleos_user32_link_spec` 5/5.
- **Run check:** `exidx_walk.c` is a freestanding program. It walks `__exidx_start..__exidx_end`, checks that entries are strictly increasing, that the last entry is the CANTUNWIND sentinel, and that a binary search finds its own functions. Linked by the Simple linker, it exits 0 under `qemu-arm-static`; so does the lld-linked build.
- **Limit:** this validates the table only. No C++ throw or `_Unwind_Backtrace` was run, because no armhf unwinder is available and GCC's libgcc_eh is not allowed.
- **Not covered:**
  - `.ARM.extab` table-pointer entries have no fixture.
  - The binding and visibility of `__exidx_start/end` were not compared with lld, which does not list them in its symtab.
  - `.ARM.attributes` and `.comment` are still dropped.
