# Linker: `name@@VER` in a relocatable object never binds `name`

- **status:** verification-pending
- **found by:** FreeBSD aarch64 static cross-link (`undefined symbol: openat`, simplelink lane)

## Defect
FreeBSD `libc.a(openat.o)` defines `openat` only as `openat@@FBSD_1.2` (`.symver`, default version) and `openat@FBSD_1.1`. `elf_parse_object` kept the literal names, so a plain `openat` reference stayed undefined. ld.lld binds the reference to the default-version definition.

## Fix
`elf_parser.spl`: a defined symbol named `x@@V` is read as `x`. A non-default `x@V` keeps its name and never satisfies `x`. Two objects that define `x@@V2` and `x@@V3` now collide as `x`, which is a duplicate definition in ld.lld too.

## Repro and prevention
- `test/01_unit/compiler/backend/linker/elf_symver_object_spec.spl`, using fixtures `symver_def_a64.o` and `symver_use_a64.o`.
- The FreeBSD aarch64 and riscv64 static hellos now link.
