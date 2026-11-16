# Internal COFF linker: mingw CRT link defects (2026-11-16)

Status: **verification-pending**. Area: `src/compiler/70.backend/linker/coff/`.

Linking llvm-mingw UCRT (20260922) `crt2.o` + `libmingw32.a`/`libmingwex.a`/ucrt
import libs with the pure-Simple COFF engine found five defects:

1. Zero-size `.data`/`.bss` output sections kept a header at the next section's
   RVA; Windows rejected the image ("%1 is not a valid Win32 application").
   Empty merged sections are now omitted (as lld does).
2. DWARF `.debug_*` input sections (long names) aborted the link. They are now
   dropped like `.debug$*` (equivalent to `-s`; lld keeps them).
3. GNU linker-defined `__CTOR_LIST__`/`__DTOR_LIST__` and
   `__RUNTIME_PSEUDO_RELOC_LIST__`/`_END__` were unresolved. The engine now
   synthesizes the `-1 ... 0` ctor/dtor tables and an empty pseudo-reloc list
   (no auto-import support yet), and folds `.ctors.N` into `.ctors`.
4. A relocation naming an external symbol whose own COMDAT copy lost selection
   (mingw `.refptr.*`) failed with "defined in a removed COFF section"; it now
   resolves to the winning definition.
5. ARM64 TLS `add xN, xN, :secrel_hi12:sym, lsl #12` (SECREL_HIGH12A) was
   rejected for its shift bit.

Repro/prevention: `test/01_unit/compiler/backend/linker/coff_mingw_crt_spec.spl`
(5/7 fail on the pre-fix linker, 7/7 pass after).

Evidence: x64 CRT+`__thread` hello linked by the engine runs on Windows 11
(`hello from crt tls=42`, ASLR, 31 DIR64 base relocs = lld); arm64 image headers,
9 import DLLs, TLS directory and 29 base relocs match lld via `llvm-readobj`.

Remaining known differences from lld: no section merging (`.xdata`, `.CRT`,
`.00cfg`, `.ctors` stay separate), two `.bss` headers (common symbols), import
thunks in a separate `.text$im` section, no `.buildid`, no DWARF.
Not covered: native arm64 run (no arm64 host), Simple-language hello (no
windows-gnu `libsimple_runtime.a` available on this host), auto-import.
