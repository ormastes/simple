# ELF boot linker copied SHF_MERGE|SHF_STRINGS sections verbatim

- **Status:** verification-pending
- **Date:** 2026-11-18
- **Area:** `src/compiler/70.backend/linker/elf/elf_boot_link.spl`

## Symptom
The bare-metal/boot linker concatenated mergeable string sections without deduplicating them. Duplicate literals survived (aarch64 fixture: `.rodata` 70 bytes vs ld.lld's 45), and the `.text` and symbol addresses differed from ld.lld. `elf_static_link` already pooled them through the shared `linker/elf/merge_strings.spl`.

## Fix
`elf_boot_link` reuses `merge_strings.spl` (`elf_merge_sections`, `elf_merge_offset`, `elf_unmerge_relocated`) with one pool per output-section group. Symbols, GOT entries, `.symtab` values and section-symbol relocations are remapped into the pool. x86 executable gaps are filled with `0xCC`, as ld.lld does.

## Evidence
`elf_boot_link_merge_spec.spl` went from 0/6 to 6/6. The `.rodata` and `.text` slices and symbol addresses are byte-identical to ld.lld for aarch64 and x86_64 (fixtures and recipe in `test/fixtures/linker/elf/RECIPE.md`). Existing boot, riscv64 and arm32 specs are unchanged. `elf_exec_writer_spec` has 13 failures that predate this change.

Time and RSS (seed, whole `elf_boot_link_spec` run): 21.2 s before, 21.8 s after; 237 MB peak both times.

## Open
- No riscv64 merge fixture yet.
- No x86_64 GOTPCRELX relaxation (separate gap).
