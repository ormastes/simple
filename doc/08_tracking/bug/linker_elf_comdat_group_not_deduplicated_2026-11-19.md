# Linker: ELF COMDAT section groups not deduplicated

- **status:** verification-pending
- **found by:** FreeBSD cross-link structural compare against ld.lld (simplelink lane). The output had a duplicate `NT_FREEBSD_ABI_TAG`.

## Defect
FreeBSD `crt1.o` and `crti.o` both carry `.note.tag` in COMDAT group `.freebsd.noteG`. The ELF linker kept every copy, because only symbol-level COMDAT tolerance existed in `sym_resolver`. ld.lld keeps only the first object's group.

## Fix
`elf_discard_duplicate_groups` (`elf/elf_static_link.spl`) runs after section GC. In link order, the first object that provides a group signature owns it, and the same group's sections in later objects are dropped.

## Repro and prevention
`elf_symver_object_spec.spl` "keeps one copy of a COMDAT group present in two objects", using fixtures `comdat_note_{a,b}_a64.o`. The FreeBSD aarch64 and riscv64 cells now match ld.lld's three-note `.note.tag`.
