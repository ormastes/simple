# Item4 RISC-V phase-4 continuation matrix

Owner: `/root/linker_acceptance`; integration/review owner: `/root`.
Worktree: `C:/dev/simple-item4-linker-acceptance-20261003`.
Branch: `work/item4-riscv-phase4-20261003`.
Base/expected release: `94a16103a5baeefad8bc7688e70b43b75dcf2914`.
Sidecars: N/A. This lane does not alter the common scope or ownership plan.

**Phase-4 readiness is not established.** Source implementation, authored test
code, source review and executed acceptance are separate columns. Existing
runtime diagnostic attempts are capped at three; no retry or seed substitution
is authorized. Every Simple scenario remains UNRUN until independent admitted
runtime evidence exists.

| Work item | Integrated production path | Test authority | Current gap |
|---|---|---|---|
| RV64 static ELF, archives, paired PCREL, branches, arithmetic, GOT/PLT32 | `elf_static_link` plus relocation scan/engine | `item4_riscv_static_link_acceptance_spec.spl` | Source present; native/SSpec execution UNRUN |
| ULEB128 SET/SUB pairs | Original-section validation, post-layout pair resolution and fixed-size patch | Same static spec | Source present; execution UNRUN |
| ALIGN padding | Pre-resolution raw-table normalization and reparse | Same static spec | Admits executable PROGBITS with covering section alignment and canonical NOPs; no instruction-size call shrinking |
| Attribute compatibility and output | Selected-object merge before layout; nonallocated output metadata before final hash | `item4_riscv_attributes_spec.spl` | Core/common-Z ISA catalog implemented; broader extension catalog, unknown vendor/scope/tag policies remain explicit admission gaps |
| Instruction relaxation | Existing ALIGN normalizer only; CALL pairs remain full size | Existing RELAX retention scenario | Iterative CALL/JAL/compressed relaxation not implemented |
| RV64 static local-exec TLS | Existing PT_TLS layout, RISC-V TP-relative classification and HI20/LO12/ADD application; defined ELF TLS symbols use block offsets on all targets | `item4_riscv_tls_spec.spl`, real RV64/x64/A64 objects | Source present; SSpec and thread runtime execution UNRUN; dynamic/GD/IE/TLSDESC remain open |
| RV64 dynamic/PIE/TLS | Driver currently rejects these modes | Explicit rejection controls | Dynamic PLT/GOT/relocation/TLS integration still required |
| RV32 complete ELF driver | Context-free RV32 relocations exist; ELF driver rejects RV32 | Rejection plus relocation helper coverage | ELF32 layout/writer/symbol/relocation pipeline still required |
| Full compiler/application runs | Typed file adapter reaches RV64 static driver | Broader item4 product acceptance | Execution and runtime admission pending |
| Bounded memory and performance | Current RV path uses resident arrays | Separate bounded lane | This lane cannot certify bounded execution or timing/RSS targets |

Attribute policy source: [RISC-V psABI](https://github.com/riscv-non-isa/riscv-elf-psabi-doc/blob/master/riscv-elf.adoc).
ISA scope is explicit in `riscv_arch_attributes.spl`; unsupported extensions
fail rather than being discarded. LLVM21 fixture checks confirm core union,
atomic merge and f/zfinx incompatibility. LLVM21 does not understand tag16;
the x3 compatibility oracle follows the newer psABI and awaits execution.

The [attribute manual](../../../06_spec/03_system/app/compiler/feature/item4_riscv_attributes_spec.md)
is authored, not runner-generated. Root review and admitted generation remain
required. No entry in this matrix authorizes dropping unfinished requirements.
