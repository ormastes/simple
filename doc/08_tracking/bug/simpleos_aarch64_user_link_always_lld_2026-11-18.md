# SimpleOS aarch64 user link ignored the internal linker (2026-11-18)

- status: verification-pending
- area: compiler / 70.backend / linker
- lane: ssos

## Symptom
`link_simpleos_user_64("aarch64", ...)` in
`src/compiler/70.backend/backend/simpleos_native_linkers.spl` always ran
`ld.lld`. It did that even when `simpleos_uses_internal_linker()` selected the
in-house engine. The x86_64 and arm64-kernel paths already honoured that
selection.

## Fix
When the internal linker is selected, the aarch64 user path now calls
`link_simpleos_internal` with the same inputs, in the same order, as
`simpleos_user_link_args_for_arch`: crt0.o, the entry object, the module-init
object, the user objects, and the core archive plus `libsimpleos_all.a` as a
group, with the `--wrap` flag.

## Repro / prevention
`test/01_unit/compiler/backend/linker/simpleos_internal_entry_spec.spl`:
- the new aarch64 case links the fixtures `crt0_a64.o` and `main_a64.o` with
  the sysroot script;
- it expects ET_EXEC, EM_AARCH64 and entry `0x50000000`, matching the ld.lld
  reference in `test/fixtures/linker/simpleos/RECIPE.md`;
- the existing x86_64 case covers the sibling path.

## Open
- AAVMF in-guest boot of an internally linked aarch64 user ELF: not run yet.
- riscv64: `internal_link_simpleos` refuses non-x86_64/arm64 targets. Waits on
  the sbm-rv64 shared RISC-V reloc module.
