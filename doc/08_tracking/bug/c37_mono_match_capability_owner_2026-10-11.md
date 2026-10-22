# Match-result capability loses its nominal owner

Issue: https://github.com/ormastes/simple/issues/3063

Status: OPEN source workaround. Actual unchanged-source C37 replay still fails; changed-candidate native execution remains pending.

## Actual retained evidence

C36 producer `5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235`
compiling frozen C37 source `c9cb8d6ac95ab64c95dc74c46772d2c60002271e` passed
HIR, then failed MIR with one diagnostic: ConcreteType.Pointer payload mismatch
at field 1. Elapsed time was 52.183 seconds; no object was produced. Receipts:
C06 `build/native_probe/phase3-whole-20261011-c06/manual-c37-reviewed-source-c36-producer/mono-util/`.

Read-only auxiliary decoding consumed all 47 cached HIR streams completely.
Historical/current generated codec content has the identical SHA-256
`225761871369956569d800d6d2c56b98cb601277a8cc9393dfafc4be8018039a`.
In mono_pointer_concrete, Pointer field capability expects Named(SymbolId78),
ReferenceCapability from compiler.mono.monomorphize.types. All four emitted
match arms carry EnumLit owner Named78 (Isolated, Exclusive, Exclusive, Shared).
Local capability170 has no symbol type, its Let has no annotation, MatchCase
has_type_ is false, and the final argument is untyped NamedVar170. No differing
owner or capability mapping was found.

Audits and exact JSON extraction are under C06
`build/native_probe/phase3-whole-20261011-c06/mono-util-pointer-owner-triage/`:
`decode-audit-v2.json`, `owner-summary.json`, `mono-pointer-function.json`, and
`read_hir_cache_v2.py`. The first diagnostic JSON exporter rendered all SymbolId
dictionary keys identically; v2 preserves their structured IDs. Only v2 output
supports the ownership comparison. This auxiliary decoder is not a qualified
compiler and provides no MIR-local or runtime execution evidence.

## Narrow workaround and limits

The local now explicitly declares its existing ReferenceCapability owner.
The mapping is unchanged: Unique→Isolated; BorrowMut/RawMut→Exclusive; all other
kinds→Shared. These same mappings existed before the adapter migration.
Strict payload validation remains unchanged. Existing Atomic/Weak parser
conversion conventions are retained; this does not establish their downstream
HIR capability semantics or add unsupported Handle representation.

Source corroboration: match_result_mir_type defaults absent expected type to
i64, and the merge remembers nominal HIR ownership when an expected type exists.
This supports a missing match-result owner diagnosis but is not a native trace
of the rejected MIR local. Subsequent C37 producer replay on frozen 67137 retains the same payload mismatch,
so the newer producer does not by itself resolve this util failure. This source
candidate remains outside the frozen/cutoff batch and has not been compiled.

## Authored checks, not executed

The adapter SSpec and standalone native fixture exercise all seven representable
pointer kinds and nonidentity T→String substitution. The native fixture checks
kind, capability and leaf separately, exits 11–17 on a failed case, and emits its
PASS marker only after all seven actual calls succeed. No native or SSpec run
was launched. Coordinated source entry: src/compiler/40.mono/monomorphize/util.spl;
behavior entry: test/fixtures/compiler/mono_capability_owner/main.spl. Bind any
future cache/evidence to exact source, admitted producer and phase identities.

Canonical registration: `mono_match_capability_owner_2026_10_11`, OPEN GitHub #3063. Source `cf9405485cd431400e8168c4fd0cb411273d3141` maps to isolated local integration `10bf6b35725a923acdafb9a99e4cb801dc74f9d4`; release landing not established.

Actual newer-producer result: Actual C37 producer 35d0990fb5bc30d3fea07e36d97122b3d2ab4a18b64985b626c54d897d70d666 compiling frozen 67137f4fb7c5856d39717576e4c2ef84a4deeca7 still fails MIR ConcreteType.Pointer payload mismatch at1 after51.86425335495733seconds; source/runtime guards match and no object. This confirms the failure persists after the C36 producer upgrade. Proposed explicit ReferenceCapability local workaround has source review only; changed candidate HIR/MIR/object/runtime remain PENDING. Receipt: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-next-source-c37-producer/mono-util/result.json`.

Removal: Permanent match-result nominal owner propagation repair; restore inferred local only after original-form actual util HIR/MIR/object and seven pointer-kind/nonidentity substitution native controls pass. Preserve exact existing kind-to-capability mapping and strict enum payload validation. Keep OPEN; no automatic retirement or stage admission.
