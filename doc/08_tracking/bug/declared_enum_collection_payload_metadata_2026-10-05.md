# Declared enum collection payload metadata (2026-10-05)

Status: source fix prepared; native UNRUN. Related actual failure is
progressive-real-tools-916-p2-3bd-streaming20/cranelift-001-slang-pack:
producer 3bd458857152a0c1be96b08f21c87ebd686c3f155a87f0f0eb7633d1bd2b07cb,
source916be6, compile1 after343.10s, MIR reached, link/run not reached.

Confirmed source defect: decode_declared_enum_payload_slot remembered the HIR
type of a user enum payload but omitted runtime_array_locals/runtime_dict_locals
and element metadata. The caller separately marked arrays only when
result_payload_type was present (built-in Result), excluding SdnValue.Array.
Native iteration requires collection provenance; an erased I64 alone is not an
array. The common decoder now records declared Array/Slice/Dict provenance and
its element/value MIR type, preserving the same tagged handle (no cast/unbox).
Scalar payloads are not reclassified. No constructor compatibility guard changes.

Two MIR regression cases assert original handle identity, array versus dict
separation, element types, nested slice metadata, and scalar non-admission.
The native fixture enum_collection_payload/main.spl tests actual pattern-based
array iteration (including empty), dict keys/value lookup, scalar case and
source collection preservation; requires exit0 plus exact5-check summary.
No native execution or memory/performance improvement is claimed. Product delta
adds bounded metadata inserts per collection extraction, no runtime allocation
or instructions; native memory/performance measurements remain pending.

The complete slang_pack failure is NOT claimed fixed. Remaining groups:
- Array/Dict constructor payload type mismatch (qualified owner identity needs
  investigation: foreign HirEnum metadata and raw Named SymbolId comparison).
- to_int unresolved (receiver metadata must be traced).
- duplicate wildcard/binding default arms (exact failing functions not isolated).
New3bd test-builder generator/verdict also failed; duplicate imported globals
remain an independent group, not explained by this collection repair.
