# Static ELF engine merged RISC-V .sdata/.sbss into .data/.bss (wrong __global_pointer$)

- **Status:** verification-pending
- **Date:** 2026-11-19
- **Found by:** ssos lane, SimpleOS riscv32 user link compared with ld.lld 18.1.3

## Symptom

A riscv32 C hello (`build/os/sysroot-riscv32`) linked by ld.lld has the output sections
`.sdata`, `.sbss` and `.bss`. The Simple linker (static ELF32 engine) wrote `.data` and `.bss`.
`elf_static_link.spl` defines `__global_pointer$` as `.sdata + 0x800`, the same as ld.lld. With
no `.sdata` output section, that silently fell back to `ELF header + 0x800`, so any
gp-relative code would address the wrong memory.

## Cause

`elf_out_name` sent every writable PROGBITS section to `.data` and every NOBITS section to
`.bss`. ld.lld keeps the `.sdata`/`.sbss` prefixes as their own output sections, with `.sbss`
before `.bss`.

## Fix

- `elf_out_name` maps `.sdata*` to `.sdata` and `.sbss*` to `.sbss`.
- `elf_out_rank` puts `.sbss` (40) before the other NOBITS sections (41). `.sdata` keeps the
  default RW rank, which comes after `.data`.

## Tests

- Repro: `test/01_unit/compiler/backend/linker/simpleos_user32_link_spec.spl` asserts that
  the riscv32 output has `.sdata` and no `.data`. `counter` comes from `main32.c` built for
  rv32.
- Similar-pattern regression run: `elf_riscv32_static_spec`, `elf_riscv64_dynamic_spec`,
  `elf_static_link_spec`, `elf_got_static_spec`, `elf_link_parallel_elf32_spec`.

## Still divergent (filed, not fixed here)

- ld.lld emits a PT_RISCV_ATTRIBUTES program header for `.riscv.attributes`; the engine
  keeps the section and writes no program header.
- PT_PHDR, `__bss_start` and the stale UND globals from GC'd sections: see
  `elf_static_exec_missing_pt_phdr_and_x86_trap_fill_2026-11-19.md`.
