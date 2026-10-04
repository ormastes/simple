# RV64 static initial-exec TLS verification

STATUS: FAIL — full item4 and Phase 4 remain incomplete.

Base: `75076715f57c7c9f20e98019a4a9ec5b1bdc0d0d`. This continuation implements
R_RISCV_TLS_GOT_HI20 with paired PCREL_LO12 and a GOT entry containing the
thread-pointer-relative offset of a defined TLS symbol. It uses the existing
static ELF link path; it does not implement RV32, dynamic TLS or relaxation.

Prerequisite finding: `elf_symref` discards defined symbol types by writing zero
into `ElfScanRef.stype`, while the existing RV64 local-exec branch requires type
6. The repair must preserve the actual winning definition type, not infer TLS
from the reference or relocation. Initial-exec and ordinary address GOT entries
also need distinct identities; the old shared key can alias their payloads.

Independent review additionally found that the layout can publish PT_TLS with
nonzero address/alignment residue. RISC-V IE and LE thread-pointer offsets must
include that residue while emitted STT_TLS values remain TLS-block-relative.
Three resolver scenarios were authored before the resolver field implementation:
actual ELF type conversion, strong/weak selection in both orders, and common
storage coalescing. Private helpers are distinct from full-link fixture helpers.

Test-first acceptance must inspect the real full-link output: decoded AUIPC and
paired low instruction targets, GOT payloads, PT_TLS, aligned nonzero offsets,
repeated references, selected archive definitions and rejection diagnostics.
An external fixture assembler establishes input bytes only, not a successful
Simple link. Source review and externally linked oracle images do not establish
native Simple execution.

Native Simple compilation/tests, canonical docgen, coverage, core/lib/MCP checks,
native smoke and NFR measurements remain UNRUN. The inspected release runtime
directories remain absent; no additional capped runtime build was attempted.
Every remaining item in `item4_verification_readiness.md` stays in scope.

Integrated source outcome: four production files implement the real static
link path. Thirteen new scenario declarations comprise nine full-link cases,
one scanner allocation contract and three resolver cases. The full-link tests
include IE and LE nonzero-residue instruction oracles, archive extraction,
winning-definition type, repeated IE slots, ordinary GOT coexistence and
malformed addends/types/pairs. The scanner test separately proves same-key
payload-domain isolation; it does not pretend to be an ABI-admitted object.

Independent source review found no P0/P1 in core and test commits. Root review
renamed a production helper, separated resolver-test helper names, and avoided
constructing GOT keys for non-GOT relocations. LLVM fixture assembly/inspection
succeeded, which verifies fixture construction only. Simple execution remains
UNRUN. Test-first here records source ordering, not observed RED/GREEN runs.
