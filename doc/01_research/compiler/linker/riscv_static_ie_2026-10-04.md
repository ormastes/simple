# RV64 static initial-exec TLS: local and domain research

Inspected release: `75076715f57`, 2026-10-04. Owner: linker_research.
Session/worktree: `C:/dev/simple-item4-riscv-ie-docs-20261004`;
branch: `work/item4-riscv-ie-docs-20261004`; target: release/1.0.
Scope: documents only. Runtime qualification remains UNRUN.

## Local evidence

In `src/compiler/70.backend/linker/elf/reloc_scan.spl:72`, the RV64
classifier admits ordinary GOT relocations 20/41 but lacks type 21. The scanner
already has `RC_TLS_IE`, used by other targets. Its GOT allocation maps use
`r.key`; adding IE classification without considering key identity risks
conflating address and TP-offset payloads.

`elf/riscv_link_support.spl:63` indexes only high relocations 20/23.
`elf/elf_static_link.spl:1616` redirects a paired low relocation to the GOT
only for high type 20. Both need type 21 integration. The driver already writes
defined IE GOT payloads through `elf_tls_tprel`; its RV64 branch at line 898
returns the address minus TLS image start. Tests must independently verify the
TLS alignment that makes that formula valid. Existing dynamic-mode admission,
TLS symbol validation, section placement and metadata stay authoritative.

## Domain evidence

The [published RISC-V psABI](https://riscv-non-isa.github.io/riscv-elf-psabi-doc/)
(September 24, 2026 development draft; searched 2026-10-04) assigns 21 to
TLS_GOT_HI20 and requires zero addend. Its paired PCREL_LO12_I relocation uses
the high relocation's displacement and also requires zero addend. IE loads a
TP-relative offset from a GOT slot. Variant I places TP after the TCB.
The indexed GitHub source excerpt lagged the published page's explicit
high-addend wording; use the published page for this restriction.

[LLD InputSection.cpp at c49af813](https://llvm.googlesource.com/llvm-project/lld/+/c49af813ca6db8f8c74529efcc407ac012a0c231/ELF/InputSection.cpp)
computes the RISC-V TP offset from the TLS symbol value plus the TLS segment
address residue modulo alignment. Consequently a zero-residue image has the
symbol's TLS-block offset as its static GOT value. This is source evidence,
not an executed comparison of the Simple implementation.

## Derived acceptance constraints

Use assembler-produced RV64 fixtures with initialized and zero-fill TLS at
nonzero offsets. Inspect the actual high/low relocation records first. Decode
the emitted AUIPC and LD independently: their combined address must point to
the intended GOT word, whose value equals the expected TP offset. Check PT_TLS
alignment, filesz/memsz, initialized bytes and TLS symbol offsets. An ordinary
GOT load in the same image must still yield an address; repeated IE references
must select the same appropriate slot. Reject a non-TLS target, missing pair,
nonzero high/low addend, and unsupported dynamic use with real errors.

These are requirements for this existing static TLS gap. They do not authorize
new runtime trust, provider registration, IE relaxation, RV32, or dynamic TLS.
