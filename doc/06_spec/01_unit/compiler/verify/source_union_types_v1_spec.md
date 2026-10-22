# Source union type map — authored manual

Requirement: REQ-C2-UNION-TRANSPORT-001. Status: **UNRUN**; this manual records
authored direct API assertions, not generated execution evidence.

`source_union_types_v1_spec.spl` exercises the actual invocation map and module
registry. Its sixteen scenarios cover canonical/synth-owner shape parity, reordered
identity reuse, nested and Optional membership with a one-element Unit payload,
singleton and zero membership, refusal of effect-bearing Function members before
key generation, unsupported outer carriers, direct function-signature conversion
with effects retained, registry ownership mismatch, missing nominal ownership,
unused malformed synthetic declarations, and exact/one-less member,
key and registry ceilings.

Revision2 adds regressions for all three cycle1 findings: exact zero-argument
lookup of already-tagged unions; dictionary/registry/declaration symbol identity
including unused enum rows; completed exact-structure plan reuse before flatten,
key and sort work; and rebuilt Function-root copy reservation.

The structure cache compares admitted immutable type shapes, excluding source
spans, under node/work debits. It uses no pointer identity, inferred hash identity
or source-name shortcut. For one existing `Union([i64, Bool])` plan, an identical
freshly constructed occurrence spends exactly three node and ten work debits,
with no additional member, key, copy or registry debits. A new reordered spelling
receives first admission and a retained plan; subsequent occurrences reuse it.
Changed members receive fresh admission. The exact/one-less Function copy oracle
includes both a zero-parameter ordinary signature and a rewritten union
parameter/result signature.

The mapper constructs the same `HirEnum` fields as the existing unexported
`synth_union_enum_normalized_with_symbols` helper. It uses the existing canonical
terminal-key helper only after rejecting every unsupported terminal shape. The
shared helper and export surface remain unchanged. The parity oracle checks the
actual existing canonical and synth-owner output; registry IDs are compared to
the actual admitted module rows rather than assuming preferred hash IDs.

Budget counters are logical conservative debits. They do not measure allocation
bytes, RSS or runtime latency. Parser, MIR, Lean and native execution remain
separate acceptance gates.
