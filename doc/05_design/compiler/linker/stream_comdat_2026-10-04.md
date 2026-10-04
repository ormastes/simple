# Streamed ELF section groups and COMDAT

Status: design/research; Simple execution UNRUN. Scope is retained static ELF
section-group semantics within item 4, not COFF COMDAT selection modes.

## Session and existing code

Owner/session: `/root/linker_research`, `item4-stream-comdat-docs-20261004`.
Reused clean worktree: `C:/dev/simple-item4-stream-got-docs-20261004`.
Branch: `work/item4-stream-comdat-docs-20261004`; target `origin/release/1.0`;
base/expected target `07c4fb746ccbdd06be1934662cc5dcad9b7b4046`.
Only this document is owned here; root integrates, runtime implements, acceptance
authors specs. Sidecars N/A. No runtime restart or source mutation.

`elf/stream_inputs.spl` rejects SHT_GROUP (17) and SHF_GROUP (0x200).
`elf/elf_static_link.spl` explicitly documents no COMDAT deduplication; searches
find implemented selection in `coff/coff_link.spl`, not a reusable ELF owner.
Do not claim fast ELF parity for this new behavior or transplant COFF selection
policies into ELF groups.

## ABI and integration contract

The [ELF gABI section-group rules](https://refspecs.linuxfoundation.org/elf/gabi4%2B/ch4.sheader.html)
identify groups through the symbol table selected by sh_link and the signature
symbol selected by sh_info. Group names do not define identity. The word array
starts with flags, followed by section indices. Members must have SHF_GROUP;
discarding a group discards all its members. The
[current gABI sections specification](https://gabi.xinuos.com/elf/03-sheader.html)
also restricts SHF_GROUP/SHT_GROUP to relocatable inputs. Sources accessed
2026-10-04.

Support flags 0 (ordinary group retained) and 1 (COMDAT first signature wins),
reject unknown flags explicitly. Signature identity is exact name; do not require
GLOBAL binding because signatures can be LOCAL. Validate symbol table/index,
payload range and word shape, member bounds/uniqueness, no group self-membership
or nested group headers, no membership shared across groups, and consistent
SHF_GROUP ownership. Accept flags-only groups (size 4) as empty no-ops; exclude
them from winner competition, matching the GNU experiment below.

Selection is deterministic in retained object/group order. Generic groups do not
deduplicate. A shared kept-section predicate must govern definition lookup,
archive candidates, ordinary/COMMON/GOT layout, relocation scans, payload output,
and symbol address resolution. Omitting bytes alone is insufficient: losing
strong definitions must not cause duplicate-definition errors or win lookup;
losing relocation tables must not allocate GOT slots or apply patches.

The gABI converts discarded-group GLOBAL/WEAK definitions to undefined symbols;
discarded LOCAL definitions cannot supply surviving outside references. The
gABI forbids outside-group LOCAL references generally, but GNU accepts a live
outside relocation to a retained LOCAL group member. Preserve that compatible
kept-member behavior; do not introduce a broader rejection in this slice. Retain
undefined symbol records even when only discarded members referenced them.
Distinguish archive demand from final missing-symbol diagnostics. Root selected
the following policy after the external probes below: existing undefined records
retain archive demand; final errors require live allocated relocation references
(or the entry root). Plain unused undefined declarations do not fail a final link.
The stream omits nonallocated sections, unlike GNU's ordinary debug output.
Discarded definitions do not synthesize new archive demand. Their live outside
references still diagnose missing definitions unless a winner/provider was
selected independently; this preserves the observed GNU archive behavior.

Keep all scans charged and cancellable, using bounded auxiliary state rather
than a resident per-section acceptance matrix. Repeated section/group/member
queries nested inside symbol and GOT rescans may grow to high polynomial work.
Finite quotas guarantee termination, not acceptable latency or whole-job RSS.
Representative compiler-generated grouped fixtures must measure work counts,
elapsed time and peak RSS after runtime admission. ITEM4-REQ-009 fast-image/digest
parity remains open because the resident fast ELF engine lacks COMDAT support.
Validation runs before selection
can hide malformed groups. Keep explicit mutable owner transitions and preserve
transactional destination publication. Public stream link API remains unchanged;
internal helper names/ownership are frozen by root and runtime before code.

## GNU binutils 2.46 experiments

Task-owned `build/comdat-oracle` sources use real GNU as section syntax with a
shared COMDAT signature `sig`, then GNU ld static links inspected by readelf.
The LF-normalized `run.sh` records exit statuses; an earlier shell invocation
had unreliable status interpolation and is not the status oracle.

| Input | Observed result |
|---|---|
| winner A then loser B, only B references missing | exit 0 |
| B then A, so missing reference survives | exit 1, undefined missing |
| Plain unused GLOBAL undefined declaration | exit 0 |
| A, B, then archive providing missing | exit 0; provider and pulled_marker present |
| Losing group defines extra loser_only, no outside reference | exit 0 |
| Live outside relocation to discarded loser_only | exit 1, undefined loser_only |
| Same live reference plus later provider archive | exit 1; BFD did not extract replacement |
| Undefined reference solely in retained .debug_info | exit 1 |
| Outside reference to retained LOCAL group member | exit 0, actual LOCAL relocation resolves |
| Outside reference to discarded WEAK definition | exit 0, pointer becomes zero |

Thus dead-group reference suppression does not justify suppressing archive
extraction. Discarded-definition replacement through an archive is a distinct
edge case: the selected implementation must not invent demand from a discarded
definition. Debug-only
undefined policy likewise depends on whether the profile emits debug sections.
These experiments executed external assembler/linker tools, not Simple or the
resulting machine code; they provide no runtime PASS.

A checked mutation of a real assembler group changed sh_size to 4 and removed
SHF_GROUP from its former member. GNU readelf reported a zero-member COMDAT group;
GNU ld accepted it. Placing it before a nonempty group with the same signature
still retained the nonempty group's `foo` definition. This supports accepting
empty groups without reserving their signature. A minimum of eight bytes would
reject a GNU-accepted input without a demonstrated ABI requirement.

## Acceptance obligations

Use actual grouped text/data/relocation fixtures with distinguishable winner
bytes and independently decoded retained pointers. Reverse input order to prove
first selection, use distinct signatures to prove independent retention, and
flags 0 to prove ordinary groups are not deduplicated. Include LOCAL signatures.
Check losing bytes, relocation effects and GOT slots are all absent atomically.

Cover live outside GLOBAL references binding to the winner, malformed outside
references to discarded LOCAL definitions failing, retained LOCAL references
succeeding, and discarded WEAK definitions resolving as undefined weak zero.
Cover discarded-only undefined links succeeding without a
provider, and the same input extracting a supplied archive provider. Preserve
entry demand and distinguish unused undefined declarations. Include archive
members selected for another symbol that carry competing groups.

Mutate checked real group words/headers for invalid flags, sizes, links/signatures,
duplicate/out-of-range/multiply-owned members, missing SHF_GROUP, and group-header
membership. Assert named failures and unchanged destination. Direct group scans
must exercise quota/cancellation after real inputs open, then close original
owners. Compare narrow output windows and exact selected extents; no fabricated
booleans or placeholder PASS. Tests precede source implementation.

## External runtime observation

PID 45936 was observed running the bootstrap-seed candidate at
`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/llvm-text-float-validation/third-seed-retry/producer/simple.exe`.
That directory's `producer.json` identifies SHA256
`5885136bf66130f384b907a4b2857c21df1e3b5bf38274f9a9f911d4c2b70308`,
`native_validated:false`, `admitted:false`. Its parent `build-result.json` and
`native-result.json` report successful operations but also `admitted:false`.

The subsequent `p2-http-client-refresh/cranelift/result.json` reports phase 2,
exit 0, source `b1668eac56919dc6c48a3dfece87333c51683eb5`, `admitted:false`.
`supervisor-result.json` agrees; `collector.receipt.env` proves completed child
exit 0, not qualification. `lineage.env` explicitly says bootstrap-seed producer,
diagnostic-monitor resource policy, and seed float cross-module defect not
qualified. No restart, interruption, rebuild, or test was performed here.

These new successful receipts do not admit a deployed self-hosted runtime.
Simple specs, canonical manuals, coverage, full compiler/MCP checks, and RSS/NFR
verification remain UNRUN. Full item 4/Phase 4 remains incomplete.
