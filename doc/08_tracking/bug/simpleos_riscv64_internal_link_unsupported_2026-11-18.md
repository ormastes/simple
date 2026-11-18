# SimpleOS riscv64 rejected by the internal linker (2026-11-18)

- status: verification-pending
- area: compiler / 70.backend / linker
- lane: ssos

## Symptom
`link_simpleos_internal(..., "simpleos-riscv64", ...)` failed with
`unsupported SimpleOS target 'simpleos-riscv64' (internal:simpleos supports
x86_64 and arm64)`. As a result, riscv64 SimpleOS user executables always went
through ld.lld.

## Fix
- `internal_link_simpleos` maps riscv64 to `RelocArch.Riscv64`. Relocations go
  through `elf_boot_link` and the shared `riscv_reloc` module (#10218).
- The linker-script parser now accepts top-level `INPUT(file, ...)` (new `LdStmtKind.InputFiles`, `BootLayoutPlan.input_files`); `internal_link_simpleos` reads those files ahead of the command-line objects, as ld.lld does. This was the second RED: `unsupported statement (at token 4 'INPUT')`.
- `link_simpleos_user_64` routes riscv64 the same way as aarch64. crt0 comes
  from the script's `INPUT()`, and the engine never relaxes, which matches
  lld's `--no-relax`.

## Repro / prevention
`test/01_unit/compiler/backend/linker/simpleos_internal_entry_spec.spl` has a
riscv64 case: script `INPUT()` crt0, ET_EXEC, EM_RISCV, entry `0x100000000`,
matching the ld.lld reference in `test/fixtures/linker/simpleos/RECIPE.md`.
- RED on the old code: it failed with the unsupported-target error.
- Sibling cases: x86_64 and aarch64.

## Open
- OpenSBI in-guest boot of an internally linked riscv64 user ELF: not run.

## Follow-up (2026-11-18)
- A bare `INPUT(name)` is now looked up through `config.library_paths` (`-L`)
  after the path as given, as ld.lld does. RED before the fix: `SimpleOS script
  INPUT crt0_rv64.o cannot be read`.
- New coverage in `simpleos_internal_entry_spec.spl`:
  - linking a `-l` static archive through the in-house SimpleOS path, with a
    negative case where the archive is missing;
  - the bare-INPUT miss case.

  The archive cases pin behaviour that already worked, so they passed on the
  first run.
- Removed the unused `InternalSimpleOsFlags.archive_group` field. Archive
  closure always runs to a fixpoint (`archive_closure.spl`), so group flags are
  only checked for balance.
