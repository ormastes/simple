# Linker: weak _DYNAMIC rejected in a static ET_EXEC

- **status:** verification-pending (fixed in PR #10269)
- **found by:** rv32 musl static link (simplelink lane)

## Defect
musl's `crt1` makes a weak hidden reference to `_DYNAMIC`. In a static ET_EXEC the Simple linker resolved that reference through the synthetic-symbol path, which errors with `undefined symbol: _DYNAMIC (output has no .dynamic)`. ld.lld leaves the symbol undefined-weak, with value 0.

## Fix
In `elf_symref` (`elf_static_link.spl`), a weak `_DYNAMIC` in `ELF_LINK_STATIC_EXEC` is `SYMREF_WEAK_ZERO`. Static PIE and the dynamic modes keep the synthetic `.dynamic` address, and a strong reference still errors.

## Repro and prevention
`test/01_unit/compiler/backend/linker/elf_riscv32_static_spec.spl` uses the fixture `weak_dynamic_rv32.o`. The rv32 musl hello runs under qemu-riscv32 and exits 42, the same as ld.lld.
