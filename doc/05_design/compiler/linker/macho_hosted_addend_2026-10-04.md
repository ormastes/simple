# Hosted ARM64 explicit-addend relocation pairs

Base `edfb6df1821ff98a0d563cca5496630cedf7789e`; existing ITEM4-REQ-004/006.
Status: frozen test-first contract; source implementation pending and all Simple
execution UNRUN. Local and domain evidence are in
`doc/01_research/{local,domain}/macho_hosted_addend_2026-10-04.md`.

## Shared operation

New acyclic `macho/relocation_pairs.spl` owns `MachORelocationPairV1` with fields
`relocation`, `explicit_addend`, `consumed`, and
`macho_relocation_pair_v1(relocations,index,arm,input_name:text)` returning a
checked result. Ordinary records consume one entry and return zero explicit
addend. ARM64 type 10 consumes two only after validating the prefix flags,
length 2, follower availability, identical address and follower type 2/3/4.
Preserve the existing named malformed-prefix/follower diagnostics, including
input identity. Invalid indices reject before indexing.

Both `relocations.spl` and `hosted_fixups.spl` use this owner. The hosted loop
classifies only the returned follower, marks its patch range once and never
interprets the prefix's signed payload as a symbol index. The final relocation
pass applies the returned sign-extended 24-bit addend exactly once, retaining
existing local-symbol/section address corrections and ISA overflow checks.

Shared static/hosted validation rejects a nonzero explicit addend combined with
a nonzero instruction-embedded addend. Zero explicit is permitted. Decode the
actual branch/page/page-offset field, including scaled load/store immediates,
without confusing opcode or register bits with addend bits. This tightens
malformed input handling consistently rather than silently changing one path.

Locally defined symbols support BRANCH26, PAGE21 and PAGEOFF12 pairs through
existing formulas. Imported branches remain valid only with both explicit and
embedded addends zero; otherwise preserve the named imported-branch error before
stub patching. Imported direct page/data addressing remains rejected. No GOT/TLV
pair followers or new dyld binding semantics are introduced.

## Test-first acceptance

Use real ARM64 object fixtures and the production hosted/file adapter, with
independent final instruction decoding: signed branch displacement, ADRP page
delta, ADD page offset and scaled load/store offset. Cover positive and negative
explicit addends crossing page boundaries, locally defined symbol resolution,
and zero-prefix imported calls reaching the actual generated stub.

Mutate proven actual relocation records for missing follower, wrong address,
prefix extern/PC-relative/width, wrong follower and repeated/overlapping patches.
Assert malformed rejection and destination preservation through the file route.
Test signed-24 boundaries at the decoder, distinguishing payload validity from
the downstream instruction's alignment/range constraints. Nonzero explicit plus
embedded input must fail in both static and hosted paths; ordinary zero-prefix
and preexisting subtractor behavior must remain valid. Imported nonzero cases
must reject rather than accidentally add to the selected stub address.

The helper reads one or two records and adds no full-image allocation. Existing
hosted image allocation and resource qualification remain separate. External
assembler/inspection receipts are fixture evidence only. Full Darwin load/run,
signing, five-host scope, SDK weak binding and item4 runtime gates remain open.

## Ownership

Runtime owns the new pair utility and two relocation consumers; acceptance owns
fixtures, executable specs and mirrored manual; research owns these evidence
documents, canonical acceptance linkage and independent final review. Root owns
integration and exact-head final review. Separate worktrees; sidecars N/A.
