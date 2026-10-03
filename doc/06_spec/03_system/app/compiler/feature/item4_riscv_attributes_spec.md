# RV64 attribute merge acceptance manual

Executable authority: `test/03_system/app/compiler/feature/item4_riscv_attributes_spec.spl`.
Requirements: ITEM4-REQ-003, ITEM4-REQ-006, ITEM4-REQ-007.

Status: **UNRUN**. This is an authored companion manual, not generated runner
output. No admitted Simple runtime is available; the existing three-attempt
diagnostic cap remains in force. The integration owner must review this manual
and regenerate it through admitted SSpec tooling before accepting execution.

| Scenario | Action | Required observable result |
|---|---|---|
| ISA and ABI union | Link clang RV64I entry with RV64IMAC provider, then reverse input order | One nonallocated SHT_RISCV_ATTRIBUTES section; canonical extension union; stack16, unaligned1, atomicA6C, gp1; identical metadata bytes |
| Stack and gp conflict | Substitute stack32 and shadow-stack providers | Named stack-alignment or x3-usage error before image emission |
| Atomic compatibility | Link A6S with A7, then mutate A6S to A6C | First output records A7; second link rejects atomic ABI conflict |
| ISA conflict | Link same-ABI RV64IF and RV64IZfinx objects | Named incompatible f/zfinx error |
| Archive admission | Link archive containing selected provider and unused incompatible duplicate | Only selected member influences stack alignment and ISA union |
| Malformed records | Mutate format, vendor, vendor length and architecture terminator | Specific bounded-parser rejection; metadata is never silently discarded |
| Build identity | Locate output GNU digest, zero it, hash the entire image | Digest covers newly emitted attributes and updated ELF section table |

Fixtures are in `test/fixtures/linker/riscv64/`. `attr_float_start.o` is built
from `attr_start.s` with `-march=rv64if`; `attr_finx_provider.o` is built from
`attr_provider.s` with `-march=rv64izfinx`. Other attribute fixtures use RV64I,
except `attr_provider.o`, which uses RV64IMAC_Zicsr. All use LP64 and clang21.1.8.
The archive contains `attr_provider.o` followed by `attr_stack32.o`.

LLD21 independently confirmed ISA/atomic/unaligned merging and rejected f/zfinx.
It warned that tag16 is unknown, so it is not evidence for the new x3 policy;
that expectation comes from the current RISC-V psABI. These fixture checks are
not Simple test results.

The implementation admits a documented finite ISA catalog. Unknown extensions,
vendors, scopes and attribute tags return named errors. Full catalog expansion,
all platform execution, performance evidence and phase-4 admission remain open.
