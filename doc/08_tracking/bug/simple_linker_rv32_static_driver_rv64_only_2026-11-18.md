# Simple linker: RV32 static ELF link rejected / RV64-only helpers

- **id:** simple_linker_rv32_static_driver_rv64_only_2026-11-18
- **status:** verification-pending
- **lane:** sbm-rv32
- **area:** src/compiler/70.backend/linker/

## Symptom
`elf_static_link(..., RelocArch.Riscv32)` returned
`elf_static_link: RV32 ELF driver is not supported`, so the bare-metal riscv32
hello could not be linked by the in-house linker even though `reloc_engine`
already applies RISC-V relocations with XLEN=32.

## Root cause (four RV64-only assumptions)
1. `elf_static_machine` failed closed for `Riscv32`; every RISC-V gate in the
   driver tested `== RelocArch.Riscv64` only (PCREL_LO pairing, ULEB, TLS).
2. `elf_riscv_flags` required ELFCLASS64 and read e_flags at offset 48.
3. `riscv_isa_merge` required an `rv64i` arch string and always emitted `rv64`.
4. `elf_append_nonalloc_section_bytes` (used for `.riscv.attributes`) only
   understood ELF64 section-header geometry.

## Fix
`elf_target_is_riscv` gates the shared RISC-V path; RV32 joins the ELFCLASS32
writer (`w32`) with merged RISC-V e_flags; `elf_riscv_flags_xlen`; XLEN-aware
ISA merge (rejects mixed rv32/rv64, implies zcf for RV32 c+f); class-aware
non-alloc section append. R_RISCV_ALIGN on RV32 fails closed explicitly.

## Tests
- Repro: `test/03_system/app/compiler/feature/rv32_static_link_acceptance_spec.spl`
  (red: "RV32 ELF driver is not supported"; green after fix).
- Similar patterns: existing RV64 `item4_riscv_static_link_acceptance_spec.spl`
  and `item4_riscv_attributes_spec.spl` re-run.

## Open
- RV32 R_RISCV_ALIGN relaxation padding (fails closed).
- Native-compiler verification and the OpenSBI fw_payload boot transcript.
