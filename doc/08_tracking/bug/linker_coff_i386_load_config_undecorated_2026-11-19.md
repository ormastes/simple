# Linker: COFF closure never loads i386 `__load_config_used`

- **status:** verification-pending
- **found by:** Opus review of the `_tls_used` closure fix (simplelink lane, PR #10291)

## Defect
`coff_archive_closure_retained_aliases` (`src/compiler/70.backend/linker/coff/archive_closure.spl`)
force-retains the load-config symbol so the CRT's load configuration directory is linked,
as lld-link does. It used the undecorated `_load_config_used`, but i386 C symbols carry an
extra underscore (`__load_config_used`; `coff_link.spl` `_coff_decorate` already decorates it
when attaching the directory). On i386 the member was never loaded, so the internal linker's
i686 image had `LoadConfigTableRVA 0` while lld's has a 0xBC-byte directory.

## Fix
The forced name is `__load_config_used` when any root object is i386.

## Repro
`test/01_unit/compiler/backend/linker/coff_archive_closure_spec.spl` — "extracts the
i386-decorated __load_config_used for an i386 link" (red before, green after). End to end:
`check-windows-pe-internal-link.shs` PASS; the i686 image now has `LoadConfigTableSize 0xBC`
like lld, and still runs natively.
