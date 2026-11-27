# Linker: executable definitions referenced by a DSO are not exported to .dynsym

- **status:** verification-pending
- **found by:** FreeBSD 14.4 arm64 QEMU run of the aarch64 FreeBSD cells (simplelink lane)

## Defect
`.dynsym` of a dynamic ET_EXEC/PIE held only undefined imports and COPY-relocated
names. A symbol the executable defines but a shared object references was never
exported. FreeBSD's `libc.so.7` references `environ` (defined by `crt1.o`), so both
Simple-linked dynamic and PIE binaries died at load:
`ld-elf.so.1: /lib/libc.so.7: Undefined symbol "environ"` (rc=1). Static and all
ld.lld cells ran (rc=42). glibc has no such back-reference, so the Linux cells
never showed it; the earlier structural check (headers/notes only) missed it.
ld.lld also exported the weak `_Jv_RegisterClasses` for the same reason.

## Fix
- `shared_object.spl`: `ElfSharedLib.needs` records each DSO's undefined
  GLOBAL/WEAK dynamic symbols.
- `elf_static_link.spl`: non-hidden executable definitions named in any `needs`
  are appended to `.dynsym` (binding/type of the definition, version index 1),
  in the GNU-hashed tail with COPY names (`elf_scan_add_exports`); they are also
  section-GC roots, like ld.lld.

## Repro
`test/01_unit/compiler/backend/linker/elf_dso_needs_export_spec.spl` with
fixtures `needenv_start_a64.{c,o}`, `needenv_lib_a64.c`, `libneedenv_a64.so.1`
(oracle: ld.lld exports `environ` GLOBAL OBJECT and `_Jv_RegisterClasses` WEAK
FUNC, not the hidden `hidden_thing`). Native verification: rerun the aarch64
FreeBSD dynamic/PIE cells in the VM.
