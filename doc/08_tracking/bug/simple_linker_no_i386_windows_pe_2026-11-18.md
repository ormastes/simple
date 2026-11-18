# Simple PE/COFF linker had no i386 (i686-w64-windows-gnu) support

- **Status:** verification-pending
- **Date:** 2026-11-18
- **Area:** `src/compiler/70.backend/linker/coff/`

## Symptom
`coff_link` accepted only AMD64 and ARM64. An i686 llvm-mingw UCRT object set (`crt2.o`, `libmingw32.a`, import libs) could not be linked in-house, although `pe_image_writer.spl` already wrote PE32 (0x10b) images for machine 0x14c.

## Fix
- `coff_object.spl`: adds machine 0x14c, the `IMAGE_REL_I386_*` set and `coff_apply_i386_relocation`. DIR32 records a HIGHLOW base reloc.
- `pe_import_builder.spl`: 4-byte ILT/IAT, ordinal flag 0x80000000, and `FF 25 abs32` thunks with HIGHLOW fixups.
- `coff_import.spl`: the NOPREFIX and UNDECORATE short-import name types.
- `coff_link.spl`: the link is parametrized by machine. i386 symbol decoration (`_`) covers the entry, `___CTOR_LIST__`/`___DTOR_LIST__`, `___ImageBase`, `__tls_used` and the pseudo-relocs. The PE32 TLS directory is 24 bytes, and CTOR/DTOR list heads are pointer sized. The latter fixed a segfault at 0xffffffff.

## Evidence
- `scripts/check/check-windows-pe-internal-link.shs`: `PASS — 3 image(s) linked by the internal PE/COFF linker, structure matches lld; native run: x86_64 i686`.
- The i686 image runs natively under WoW64 and prints `hello from simple pe linker` (rc 0).
- Link: 11264 bytes, `link_ms=299`. Peak RSS was not measured.
- `coff_i386_link_spec.spl`: 14/14. Pre-existing coff spec failures are unchanged with and without this patch.

## Known gap
lld synthesizes `_load_config_used` for i386; the mingw CRT does not define it, so our image has no load-config directory. The image runs, and the compared fields match.
