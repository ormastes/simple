# Hosted ARM64 ADDEND: local evidence

Inspected release `edfb6df1821ff98a0d563cca5496630cedf7789e`, 2026-10-04.
Existing scope: ITEM4-REQ-004/006; no new requirement selection.

`src/compiler/70.backend/linker/macho/hosted_fixups.spl` rejects relocation type
10 before ordinary symbol classification and overlap tracking. Thus a valid
hosted ARM64 input with an explicit ADDEND cannot reach image generation.
`macho/relocations.spl` already consumes that prefix in the static/final patch
pass: nonexternal, non-PC-relative, length 2, next relocation present at the same
address, follower BRANCH26/PAGE21/PAGEOFF12, payload sign-extended from 24 bits.
It currently adds explicit and instruction-embedded addends together.

`macho/hosted_link.spl` builds fixups before calling the same relocation pass.
Sharing pair decoding makes both passes classify the effective follower and
consume it once. The ADDEND payload is not a symbol-table index or an independent
patch range. Existing imported-branch handling routes calls through image-owned
stubs and rejects embedded nonzero addends; it must also reject explicit nonzero
addends rather than branch into a stub's interior.

Proposed ownership is an acyclic `macho/relocation_pairs.spl` utility imported by
both consumers. Existing object/archive resolution, layout, dyld metadata and
publication owners remain intact. Source implementation and runtime execution
were absent at this initial research point; full native qualification remains
UNRUN. See the matching domain research and detail design for the frozen contract.
