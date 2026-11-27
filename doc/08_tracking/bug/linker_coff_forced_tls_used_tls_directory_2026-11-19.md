# Linker: COFF closure force-loads mingw tlssup, emitting a TLS directory lld omits

- **status:** verification-pending
- **found by:** Windows arm64 (aarch64-w64-mingw32, llvm-mingw UCRT) structural compare vs ld.lld (simplelink lane)

## Defect
`coff_archive_closure_retained_aliases` (`src/compiler/70.backend/linker/coff/archive_closure.spl`)
force-retained `_tls_used` whenever any archive provided it. With llvm-mingw that loads
`libmingw32.a(tlssup.o)` for every program, so the internal PE/COFF linker's x86_64 and
arm64 hello images carried a TLS directory (`TLSTableRVA 0x9030, size 0x28`) plus `.tls`/`.CRT`
TLS callback data, while lld's images have none. lld-link force-resolves only
`_load_config_used`; tlssup loads only through a real reference (`_tls_index` from
`__thread` code). `check-windows-pe-internal-link.shs` did not compare the data directories,
so it passed regardless.

## Fix
Only `_load_config_used` is force-retained.

## Repro
`test/01_unit/compiler/backend/linker/coff_archive_closure_spec.spl` — "extracts
_load_config_used but not an unreferenced _tls_used" (red before, green after). End to end:
`check-windows-pe-internal-link.shs` PASS with x86_64/i686 native runs; all three internal
images now report `TLSTableRVA: 0x0` like lld.
