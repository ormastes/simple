# Simple linker: armv7/i686 hosted-glibc relocations rejected or mis-applied

- id: simple_linker_armv7_i686_hosted_relocs
- status: verification-pending
- area: src/compiler/70.backend/linker (elf_static_link, reloc_engine, elf_parser, sym_resolver, merge_strings, tls_relax)
- found: 2026-11-17 simplelink survey (xc linker matrix lane)

## Symptoms (repro: `scripts/xc/slk_link.spl` against Ubuntu 24.04 cross sysroots)

| target | input | first error before fix |
|---|---|---|
| armv7 | crt1.o / hello_libc.o | `unsupported ARM REL implicit-addend relocation type 25` |
| armv7 | libc.a | types 107 (TLS_IE32), 51 (THM_JUMP19), 24 (GOTOFF32), 96 (GOT_PREL) unsupported; `.rodata.cst4` with relocations rejected as "targets merge-section contents"; ARM `BL` to a Thumb function rejected as "branch target is not 4-byte aligned" |
| i686 | libc.a | `duplicate symbol: __x86.get_pc_thunk.*` (STB_GLOBAL in SHF_GROUP COMDAT sections) |
| i686 | libc.a | R_386_TLS_LE (17) / R_386_TLS_GOTIE (16) silently classified RC_PCREL (wrong value, no error) |

## Fix (shared modules, no per-target copies)

- `elf_parser.elf_arm_rel_addend`: full-word addends for 24/25/26/96/107/108; THM_JUMP19 decode.
- `reloc_engine`: `R_ARM_THM_JUMP19` apply+patch; `R_ARM_CALL` to a Thumb symbol interworks as `BLX` (H bit).
- `elf/reloc_scan`: ARM 26/96 -> RC_GOT, 107 -> RC_TLS_IE, 108 -> RC_TLS_LE, 51 -> RC_BRANCH; i386 16 -> RC_TLS_IE, 17 -> RC_TLS_LE.
- `elf/tls_relax.elf_tls_tpoff_variant1`: one variant-I TP formula (AArch64 TCB 16, ARM32 TCB 8).
- `elf/elf_static_link`: ARM BASE_PREL/GOT_BREL/GOTOFF32/GOT_PREL/TLS_IE32 formulas (lld ARM::getRelExpr), i386 TLS_GOTIE/TLS_LE, GOT base needed for those.
- `sym_resolver`: strong duplicates both in SHF_GROUP sections keep the first (COMDAT). The losing copy's section is still emitted (no group discard yet).
- `merge_strings.elf_unmerge_relocated`: a relocated SHF_MERGE section is placed as an ordinary section.

## Tests

- `test/01_unit/compiler/backend/linker/elf_parser_spec.spl` (hosted ARM full-word addends, THM_JUMP19 decode)
- `test/01_unit/compiler/backend/linker/reloc_engine_spec.spl` (THM_JUMP19 encode/range, BLX interworking)
- `test/01_unit/compiler/backend/linker/sym_resolver_spec.spl` (COMDAT strong dedup + non-group dup still fails)

Pre-existing failures unrelated to this change (fail identically on the base):
`elf_parser_spec` "width-correct ARM absolute and TARGET1", `sym_resolver_spec` "coalesces common definitions".

## Remaining (not fixed here)

- armv7 static glibc: ARM `B` (JUMP24) tail call to a Thumb function needs an interworking veneer (thunk); Thumb `BL` to ARM needs BLX (low-half bit 12).
- i686 static glibc: `__letf2`/`__unordtf2` undefined — compiler-rt i386 builtins ship no TF (binary128) routines; libgcc is not admissible (never GCC).
- ELF32 dynamic/PIE output (PLT/GOT/.rel.dyn/.dynamic for i386 and ARM) is gated off: "only static ET_EXEC is admitted for i386/armv7".
- COMDAT group discard (drop the losing group's sections).

## Evidence (2026-11-18, qemu-user via small_slot.sh)

| target | linker | link | run | size |
|---|---|---|---|---|
| i686 freestanding | simple | OK | rc=42 "hi" | 784 B (lld 808 B) |
| armv7 freestanding | simple | OK | rc=42 "hi" | 788 B (lld 1028 B) |
| aarch64 freestanding | simple | OK | rc=42 "hi" | 1176 B (lld 1256 B) |

ld.lld: 0.04 s, ~56 MB RSS. Simple linker (Windows seed interpreter, includes
interpreting linker source): ~9 s, ~505 MB peak RSS.

## Follow-up (PR after #10183, Opus review items 2 and 3)

- `sym_resolver`: a strong definition replacing a weak one now updates the COMDAT mark (stale mark could mask a real duplicate).
- `reloc_engine`: an existing BLX relocated against an ARM-mode target is rewritten to BL.
- Still open: item 1 (dedup by group signature + discard losing group), item 4 (THM_JUMP19 to ARM-mode target should error), armv7 interworking veneers, ELF32 dynamic/PIE.
