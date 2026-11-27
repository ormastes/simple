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

## Boot follow-up (2026-11-18, PR after #10172)
Three defects stood between #10172 and a real boot; all fixed here:
1. `elf_i386_link_*` were not exported, so `bin/simple run` rejected
   `baremetal-elf32-link.spl` (the spec runner did not enforce visibility).
2. Compiled i686 objects are PIC: `main.o`/`bm_rt32.o` use `R_386_GOTPC` +
   `R_386_GOTOFF` (no GOT slots). The raw linker now anchors the GOT at the
   image base; `R_386_GOT32`/`GOT32X` (real slots) stay rejected.
3. OVMF IA32 has no free memory at 16 MiB: AllocatePages(AllocateAddress)
   returned EFI_NOT_FOUND (EAX=0x8000000E, stub spinning). crt0_i686 is now
   position independent (GOTPC/GOTOFF) and both stubs use AnyPages.
4. i686 used `bm_rt.spl` (i64 params) -> text printed NUL-padded into rodata,
   the known 32-bit pair-ABI mismatch
   (`baremetal_32bit_i64_pair_abi_mismatch_2026-11-17.md`); i686 now uses
   `bm_rt32.spl`, and crt0 `bm_store8` reads its value at 8(%esp).

Evidence: Simple linker (`elf_i386_link_raw`, 5.2 s on Windows bin/simple.exe)
+ shared PE32 emitter -> BOOTIA32.EFI on OVMF32 pflash (q35, 256M, FAT ESP,
no -kernel, no isa-debug-exit), serial:

    hello from Simple bare metal
    n=42
    ints 0 -7 9223372036854775807 -9223372036854775808
    panic: boom

`bm_rt32.spl` native-build for i686 (simple-p2): see PR body for time/RSS.
Limit: `check-baremetal-efi-boot.shs --linker simple` needs SIMPLE_LINK_BIN
with a `run` command; neither WSL binary (simple-p2, sosrt2) has one today, so
the link + wrap ran on Windows with the WSL-built objects. Board run not
evidenced.

## Follow-up 2026-11-18: measurements and the lld lane

- Simple link (`baremetal-elf32-link.spl` via `simple.exe run`, Windows, interpreter fallback): 4.9-5.4 s wall and 501-518 MB peak working set. The output is a 134041-byte image, byte-identical to the image that booted.
- lld lane (`--linker lld`) on release/1.0.0 failed at the EFI wrap: `lld-link: undefined symbol: _image_start/_image_end`, because i386 COFF prefixes C symbols with `_`. Fixed with asm labels on the extern declarations. `efi_main` now returns `uintn`.
- After the fix, `--arch i686 --linker lld` boots on OVMF IA32 with the exact transcript (PASS). Whole check: 8:40 wall, 126 MB max RSS (WSL, small_slot).
- `elf_link_rss_budget.shs`: selftest PASS (4 fixtures). The measured run needs a natively built `elf_link_bench_driver`, which is not built in this lane (the x86_64 ELF path, not the ELF32 raw path).
