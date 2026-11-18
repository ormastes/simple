# Simple linker could not link i386 (R_386_*) bare-metal images

- **Status:** verification-pending
- **Lane:** sbm-i686 (2026-11-18)
- **Area:** `src/compiler/70.backend/linker/elf/arm32_raw_link.spl`

## Symptom
The in-house linker had no i386 path: `elf_static_link`/`elf_boot_link` cover
x86_64/aarch64 only, and the ELF32 raw-image linker (`arm32_raw_link`) rejected
any object that was not `EM_ARM`. The i686 bare-metal hello could only be linked
with `ld.lld` + `lld-link`.

## Fix
- `elf32_raw_link_parsed(objects, base, entry, is_386)` is the shared ELF32
  raw-image core; `elf_arm32_link_*` and new `elf_i386_link_*` are thin entry
  points. R_386 encoding comes from `reloc_engine` (`reloc_apply_i386`), widths
  from `reloc_patch_width`. REL implicit addends were already decoded by
  `elf_parser` (`elf_i386_rel_addend`). GOT-relative R_386 forms are rejected:
  a raw image has no GOT.
- `EM_386` added to `elf_inspect`.
- `efi_stub_i686.S`: IA32 UEFI stub that runs from the PE load address, asks
  AllocatePages(AllocateAddress) for the link base, copies the blob and jumps
  to `_start`. It follows the `pe_efi_blob` contract (len at offset 8).
- `check-baremetal-efi-boot.shs --linker simple --arch i686` links with
  `scripts/check/baremetal-elf32-link.spl` and wraps with the shared PE32
  emitter (`baremetal-efi-wrap.spl`, PR #10098). No ld.lld, no lld-link.

## Tests
- `test/01_unit/compiler/backend/linker/i386_raw_link_spec.spl` (repro: R_386_32
  and R_386_PC32 at the 16 MiB base; similar patterns: cross-machine rejection
  both ways, 32-bit overflow is an error rather than a truncation).
- `arm32_raw_link_spec.spl` unchanged: 10/13; the 3 failures are pre-existing
  (`test/fixtures/linker/arm32` is not in the tree).
