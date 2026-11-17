# elf_boot_link misplaced input-section bytes when layout order differs from section-index order

- **Status:** verification-pending
- **Found by:** lane sbm-a64 (aarch64 bare-metal hello linked by the Simple linker, booted through AAVMF)
- **Component:** `src/compiler/70.backend/linker/elf/elf_boot_link.spl` (output-contents loop)

## Symptom

The aarch64 bare-metal EFI hello, linked with `elf_boot_link` (via
`baremetal-simple-link.spl`), faulted on its first instruction under AAVMF:
`Synchronous Exception at 0x000000004C73F000` (the entry, ImageBase + 0x1000).
`llvm-objdump` of the Simple-linked ELF showed only zeros at `efi_entry`
(offset 0). The stub's real bytes (`b +0x10; .word 0`) had landed at 0xd8.
Symbols were all at the right addresses; only the content was shifted.

## Root cause

Output contents were built by appending each input section's bytes in
`(object, section-index)` order:

```
buf = write_zeros(buf, ins.off_of[flat] - buf.len())   # no-op when negative
... buf = buf.push(byte)
```

A linker script can place a lower-index input section after a higher-index one
of the same object. `efi_stub_aarch64.o` has an empty `.text` (index 2) and
`.text.boot` (index 3). `*(.text.boot) *(.text*)` puts `.text.boot` at offset 0
and the empty `.text` after every `.text.boot`. Index 2 padded the buffer past
0, so index 3's negative pad was a no-op and its bytes were appended at the end.
The same happens with `*(.data*) *(.text*)` in one output section.

## Fix

Each input section is written at its layout offset `ins.off_of[flat]`. The
buffer is grown with zeros only when it is too short.

## Tests

- Repro: `test/01_unit/compiler/backend/linker/elf_boot_link_spec.spl`,
  "places a lower-index section after a higher-index one in the same output
  section". The checked-in aarch64 fixtures are linked with `.data` before
  `.text` in one output section, and the `.data` bytes must equal those from a
  split link. RED before the fix: the section started with zeros where `[2, 0, ...]`
  was expected. GREEN after.
- Similar pattern: the only other `write_zeros(x, n - x.len())` in the linker is
  the trailing pad to `o.size` in the same loop. It only grows the buffer, so it
  is correct. `elf_static_link` does not build contents this way.
- End to end: the aarch64 EFI hello boots through AAVMF (see the sbm-a64 PR).

## Spec totals

- `elf_boot_link_spec`: 47/48. The one failure, "writes CODE_4 and CODE_6
  GOTTPOFF through one SimpleOS TLS slot", fails with or without this change
  (see `elf_boot_link_code_gottpoff_fixture_entry_2026-10-06.md`).
- Spec wall time: 22 s on the Windows seed binary.
