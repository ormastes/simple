# Simple ELF linker drops `.comment` (ld.lld keeps it)

- **Status:** verification-pending
- **Date:** 2026-11-19
- **Area:** `src/compiler/70.backend/linker/elf/elf_static_link.spl`

## Symptom
`elf_link_with_operations` discarded every input `.comment`. ld.lld 18.1.3 output for
the `test/fixtures/linker/elf/simpleos32` arm32/i686/riscv32 hello links
(`C:/dev/wt/xc-wsl-scripts/ssos_cm.sh`) has:

```
.comment  PROGBITS  size 0x42  ES 01  Flg MS  Al 1
[ 1] Ubuntu clang version 18.1.3 (1ubuntu1)     <- from *_main32.o
[28] Linker: Ubuntu LLD 18.1.3
```

## Fix
- `elf_comment_section.spl`: collects input PROGBITS `.comment`s and merges their
  NUL-terminated strings, deduplicated in first-seen order, after a leading empty
  string, then appends `Linker: Simple ELF linker`.
- `elf_nonalloc_section.spl`: `elf_append_nonalloc_section_bytes_with` sets
  `sh_flags`/`sh_entsize`; the old helper delegates with `0, 0`.
- Appended unconditionally (also under strip, as lld does) after `.ARM.attributes`,
  before the build-id digest, on both the ELF32 and sealed ELF64 paths.

The identity string is Simple's own: `.comment` records the producer, and copying
lld's string would misattribute the output.

## Known differences from lld
- Order: lld's non-tail-merge section is hash-sharded, so with many strings its
  order is not strictly first-seen. On the fixtures the bytes match up to the identity string.
- lld's offset-0 NUL is the inputs' empty piece; Simple always writes one.

## Tests
`test/01_unit/compiler/backend/linker/simpleos_user32_link_spec.spl`: arm32
`.comment` type/flags/entsize/content, and the dedup order of `elf_merge_comment_strings`.
Baseline 7/8 before the fix (the new engine `it` failed).
