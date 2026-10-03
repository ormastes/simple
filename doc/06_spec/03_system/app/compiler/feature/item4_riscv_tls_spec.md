# RV64 local-exec TLS and ELF TLS symbol values

Authored companion to `test/03_system/app/compiler/feature/item4_riscv_tls_spec.spl`.
Status: UNRUN. No admitted Simple runtime is available; this is not generated
runner evidence and records neither RED nor GREEN execution.

| Scenario | Production behavior and independent oracle |
|---|---|
| RV64 local-exec image | Link a real clang RV64 object through `elf_static_link`; inspect LUI/ADD/load/store instruction words, TLS symbol offsets, PT_TLS file/memory sizes, alignment and initialized value |
| Invalid TPREL_ADD annotation | Change the ADD opcode in the object and require a named instruction diagnostic |
| Cross-target TLS symbols | Link real x86_64 and AArch64 local-exec C objects; require global, hidden and local STT_TLS values to be block offsets, preserving bindings and visibility |

Requirements: ITEM4-REQ-004, ITEM4-REQ-005 and ITEM4-REQ-006. Setup helpers
record failures and return before unsafe reads. No scenario substitutes a
source-string check for the full static-link call.

Clang and LLD 21.1.8 fixture construction independently established RV64
instruction words `000017b7`, `004787b3`, `0007a503`, `00a7a823`, TLS offsets
4096 and 4112, and the cross-target TLS offsets 0, 8 and 16. These tool
checks are fixture evidence, not execution of the Simple implementation.

The RV64 driver admits TPREL_HI20, TPREL_LO12_I, TPREL_LO12_S and TPREL_ADD.
The ADD annotation validates an ADD with a tp source and leaves the instruction
unchanged. No relaxation or thread-pointer initialization is claimed.
R_RISCV_TLS_TPREL64 is a dynamic relocation and is not admitted as a static
input relocation. Dynamic TLS, GD/IE/TLSDESC, RV32 and full thread execution
remain required follow-up work. See the
[RISC-V psABI](https://github.com/riscv-non-isa/riscv-elf-psabi-doc/blob/master/riscv-elf.adoc).
