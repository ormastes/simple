# reloc_arch_from_machine fails open on unknown e_machine (2026-11-15)

Status: verification-pending

`src/compiler/70.backend/linker/reloc_engine.spl` `reloc_arch_from_machine`
maps every unrecognised ELF `e_machine` (including EM_386 = 3, i686) to
`RelocArch.X86_64`, so an i686 object would be patched with x86_64 formulas.

Fix: `reloc_arch_from_machine_checked` returns `Err` for unsupported machines.
Specs: `test/01_unit/compiler/backend/linker/reloc_engine_spec.spl`
("rejects i686 (EM_386)..." reproduces; "rejects an unknown machine fail-closed"
generalises; supported machines still resolve).

Remaining: i686 and armv7 have no ELF32 executable writer
(`elf/elf_exec_writer.spl` emits ELF64 only) and no `R_386_*` relocation
formulas; `elf_static_machine` (`elf/elf_static_link.spl:175`) rejects them.
