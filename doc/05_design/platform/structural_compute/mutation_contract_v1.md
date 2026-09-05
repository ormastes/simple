# MutationIR and conflict order contract v1 — frozen

Artifact group 5 of architecture §26 ("MutationIR and conflict order"), owned by
the MUTATE lane (§27). Normative source:
`doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`
§8 (MutationIR and transactional transformation) and §30.5 (verification
obligations).

Implementation: `src/lib/common/structural/mutation/`.
Gate: `test/01_unit/common/structural/mutation_contract_spec.spl`.

## Conventions

Inherited unchanged from waves 0a (ID-TAG), 0b (MAP), 0c (QUERY) and the
receipts wave:

- all integers little-endian, fixed width, no padding, no alignment;
- every enum is a u8 discriminant;
- every top-level record carries the 8-byte wire envelope
  `magic_u32 | version_u16 | reserved_u16`;
- an unknown enum discriminant, a reserved bit, or a non-zero reserved byte is a
  HARD REJECT, never a silent default;
- writers mask to width; the one signed field (`priority: i32`) is written as
  two's complement and sign-extended on read.

Invariants are enforced on **encode as well as decode**. An op or plan or
receipt that violates the contract encodes to an EMPTY buffer rather than to
bytes no decoder will accept, so an ill-formed value is unrepresentable on the
wire rather than merely unreadable.

## Types frozen here

| Type | Source | Notes |
|---|---|---|
| `MutationKind` | §8.2, verbatim | 26 variants, 0..25 |
| `ConflictPolicy` | §8.4, verbatim | 5 variants, 0..4 |
| `MutationEffect` | §8.3 `EffectSummary` | **renamed**, see below |
| `MutationOp` | §8.2, verbatim fields | 105 bytes |
| `MutationPlan` | §8.1/§8.6 | envelope + header + op run |
| `MutationCommitReceipt` | §8.5 `MutationReceipt` | **renamed**, see below |
| `EntityKindSet` | §8.3, **derived** | u32 bitset, 13 bits |
| `MutationPhase` | §8.4 key 2, **derived** | u8, 4 levels |
| `MutationOrigin` / `MutationProducer` | §8.2 field, **derived** | 9 bytes |

### Not redeclared — imported

`EntityKey`, `ArtifactId`, `SnapshotId`, `Hash128` and `snapshot_supersedes`
come from the ID-TAG lane (`structural/identity`). `DirtyMask`'s bit vocabulary
belongs to the INVALIDATE lane; §8.3's `invalidates` is frozen here as an opaque
u32 SLOT and deliberately not validated. Two declarations of one wire type is
precisely how two lanes come to disagree about a discriminant while both report
success.

### Renamed to avoid a live collision

| §8 name | Frozen as | Collides with |
|---|---|---|
| `EffectSummary` | `MutationEffect` | `compiler/00.common/structural_contracts/optimizer.spl:12` |
| `MutationReceipt` | `MutationCommitReceipt` | `compiler/00.common/structural_contracts/ports.spl:49` |

Both existing types are compiler-side projections carrying `text` digests, not
wire records. Reusing their names would have produced two incompatible
definitions of one §8 concept.

`LinkMutationKind` (`structural/resolve/resolve_types.spl`) is LINK's local
0..2 projection of the kinds it emits. It is a SEPARATE integer space; a
projection maps into `MutationKind` by name, never by reusing a discriminant.

## Layouts

```text
MutationEffect   21  reads u32 | writes u32 | creates u32 | deletes u32
                     | invalidates u32 | flags u8

MutationOrigin    9  producer u8 | stable_name u32 | source_order u32

MutationOp      105  kind u8 | phase u8 | reserved u8
                     | target EntityKey (32)
                     | expected_revision ArtifactId (20)
                     | payload u32 | precondition u32
                     | origin MutationOrigin (9)
                     | priority i32 (4) | stable_order u64 (8)
                     | effect MutationEffect (21)

MutationPlan         envelope(8) | policy u8 | schema_version u32
                     | op_count u32 | ops MutationOp * op_count

MutationCommitReceipt
                104  input_snapshot SnapshotId (28)
                     | output_snapshot SnapshotId (28)
                     | plan_hash Hash128 (16)
                     | matched_entities u64 | applied_ops u64
                     | skipped_ops u64 | conflicts u64
```

Magics: `SMEF` effect, `SMOR` origin, `SMOP` op, `SMPL` plan, `SMRC` receipt.

`payload` and `precondition` are u32 arena INDEXES with `0xffffffff` meaning
absent — the QUERY lane's ratified convention for addressing side tables from a
wire record, since an in-memory `{object_slot, generation}` handle is explicitly
"never a wire record" (`structural/resolve/resolve_types.spl`).

## Deterministic conflict order (§8.4)

The six keys, in order:

1. **target artifact/entity** — total order on `EntityKey` in WIRE-FIELD order
   (`content_hash.hi`, `content_hash.lo`, `artifact.schema_version`, `schema`,
   `local_identity`), all unsigned. Wire order is chosen so a sorter reading
   encoded bytes and a sorter reading the struct agree by construction.
2. **mutation phase** — ascending.
3. **declared priority** — **DESCENDING**, because §8.4 names the policy
   `HighestPriorityWins`.
4. **origin.stable_name** — ascending (§8.4's "plugin/advice stable name").
5. **origin.source_order** — ascending.
6. **stable_order** — ascending, unsigned.

`mutation_plan_ordered` requires each op to STRICTLY precede the next, which
also rejects two ops with identical keys. It is enforced on encode and decode,
so a plan with no deterministic application is unrepresentable on the wire.
This is what makes §30.5's "operation ordering is deterministic" and "conflicts
never depend on thread scheduling" testable rather than aspirational.

`u64` order keys are compared with `mutation_u64_lt`. Simple carries u64 in i64,
so a value above 2^63 comes back NEGATIVE with the same bit pattern; a bare `<`
would sort the top half of the space first and make the order depend on which
half a hash landed in.

`priority` is read with `mutation_i32_from_u32`. Reading it as a bare u32 turns
priority `-1` into `4294967295` and inverts `HighestPriorityWins` on every
negative priority. Both directions are pinned by a golden vector.

## Structural rules (hard rejects)

Per op:

- unknown `MutationKind`, `MutationPhase`, `MutationProducer` discriminant;
- non-zero `reserved` byte;
- a reserved `EntityKindSet` bit or a reserved `MutationEffect` flags bit;
- a phase byte that disagrees with `mutation_kind_phase(kind)`;
- an effect whose `writes | creates | deletes` does not contain the kind's own
  target entity bit. §8.3 makes the effect summary what conflict detection runs
  on, so an op that edits an entity while claiming to change nothing is
  invisible to conflict detection and still mutates the snapshot — a silently
  wrong result, which is the class of defect §8 set out to remove.

Per plan: empty op list; ops not in strict §8.4 order; unknown policy; a
declared `op_count` the buffer cannot hold (the count is widened into an `i64`
binding before it is multiplied by the record length, so the bound check cannot
wrap at 32-bit width); trailing bytes.

Per receipt (§30.5): `conflicts > skipped_ops`; `applied_ops == 0` with an
output snapshot different from the input ("failed validation leaves the original
snapshot unchanged"); `applied_ops > 0` with an output snapshot that does not
`snapshot_supersedes` the input.

## Underspecified in §8 — derivations raised for ratification

Each freezes a wire SLOT with the minimum vocabulary the surrounding sections
actually distinguish, rather than guessing silently.

### 1. `EntityKindSet` (§8.3) — never defined

Frozen as a u32 bitset (same shape and reasoning as the ratified
`MappingKindSet`). The vocabulary is derived from the only place the document
enumerates what a mutation may touch: §8.2's own kind list. Every kind names
exactly one entity class, giving 13 bits — `Tag`, `SourceText`, `SyntaxNode`,
`HirNode`, `MirInstruction`, `BasicBlock`, `LlvmInstruction`, `DomNode`,
`CssRule`, `Declaration`, `LinkDefinition`, `Relocation`, `PlacementHint`. Bits
13..31 reserved. The partition is total and disjoint over all 26 kinds, which is
what makes `mutation_kind_target_kind` total and the effect invariant
mechanically checkable.

### 2. `MutationPhase` (§8.4 key 2) — never defined

"mutation phase" appears exactly ONCE in the whole document, as ordering key 2,
with no type and no vocabulary. Key 1 is already the target entity, so key 2
cannot be the representation (that would carry no information). What it must
distinguish, once several ops share one target, is the CLASS of edit, because on
one target those classes are not commutative and priority alone cannot order
them safely.

§8.2's list partitions by verb into four classes: `Remove`(0), `Replace`(1),
`Insert`(2), `Restructure`(3). The ORDER is derived from §8.2's own insertion
semantics — `InsertSourceBefore/After` and `InsertMirBefore/After` are positioned
RELATIVE to an existing target, so ops that consume the pre-existing entity must
precede ops that anchor new material to it, and ops that change containment
wholesale run last.

The phase byte is redundant with the kind by construction and is validated
against it on both directions. That freezes the slot (a GPU sorter reads one
byte for key 2 instead of a lookup table) while making a derived field
impossible to forge into disagreement with the ratified kind.

### 3. `MutationOrigin` / `MutationProducer` (§8.2 field) — never defined

The origin must carry a stable name because §8.4 key 4 is "plugin/advice stable
name", and it must carry source order because that is key 5. Both are attributed
to the PRODUCER, so two ops from one advice cannot disagree about their
producer's identity.

The producer families are the ones §8.4 and its neighbours actually name:
`AopAdvice`(§8.4, §8.7), `OptimizerPass`(§25, §31), `CssCascade`(§8.4),
`LinkResolver`(§12/§18), `ClangAdapter`(§25's clang::transformer adapter),
`Plugin`(§8.1/§8.2's generic term, kept LAST so a named family is never
silently absorbed into it).

### 4. `plan_hash: Hash256` (§8.5) — deviates to `Hash128`

`Hash256` exists in-tree only as a `text` wrapper class
(`common/compute/placement_contracts/semantic.spl`) with no wire encoding, while
the ID-TAG lane froze `Hash128` as THE content hash of the structural wire. The
receipts wave already reused it for `MappingShardRef.content_hash` with the note
"Hash128 is reused from the ID-TAG lane rather than a new width being
introduced". This lane follows that precedent rather than minting a second hash
width. **If §8.5's 256-bit width is intentional, this needs a ratified wire
`Hash256` in the ID-TAG lane and a v2 bump here.**

### 5. Four §8.5 receipt handles deferred out of v1

`mapping_delta: MappingShardRef`, `tag_delta: TagShardRef`,
`invalidation: InvalidationSetRef` and `verification: VerificationReceipt` are
NOT on the v1 wire. Two of the four do not exist as frozen structural wire
types: `TagShardRef` is frozen only as a compiler sidecar handle
(`compiler/00.common/structural_contracts/sidecars.spl`) and
`InvalidationSetRef` is not declared anywhere. Encoding two and inventing two
would produce a record that cannot express §8.5 anyway, so v1 freezes the
numeric core and carries the four handles out-of-band. They take APPENDED slots
in a v2 bump once the ID-TAG and INVALIDATE lanes freeze them.

## Compatibility and versioning policy

Same policy as waves 0a/0b/0c:

- `MUTATION_SCHEMA_VERSION = 1`. A decoder rejects any version it does not
  equal; a version mismatch is a rejection, not a negotiation (§12.6).
- Enum discriminants are wire values. New variants take the next free number; a
  discriminant is never reused or renumbered.
- Adding a 27th `MutationKind`, a 5th `MutationPhase`, a 7th `MutationProducer`,
  a 6th `ConflictPolicy`, a 14th `EntityKindSet` bit or a 5th
  `MutationEffect` flag is a **breaking** change requiring a version bump,
  because the golden vectors pin the maximum discriminant and the reserved-bit
  masks.
- Reserved bits and reserved bytes must be zero and are hard-rejected when set.
  This is what reserves them for a future version instead of letting an old
  reader silently misinterpret a new writer.
- The record lengths (`MUTATION_EFFECT_LEN = 21`, `MUTATION_ORIGIN_LEN = 9`,
  `MUTATION_OP_LEN = 105`, `MUTATION_RECEIPT_LEN = 104`,
  `MUTATION_PLAN_HEADER_LEN = 9`) are part of the contract; changing one is a
  version bump.
- The six §8.4 ordering keys, their sequence, and the DESCENDING direction of
  key 3 are part of the contract. Changing any of them changes which snapshot a
  plan commits and is a version bump.

## Golden vectors

`test/fixtures/structural/mutation_golden_v1.spl` (Simple) and
`test/fixtures/structural/mutation_golden_v1.sdn` (language-neutral mirror, for
a Rust/C++ bridge or an external validator).

Every hex string was derived **by hand from the layout tables above**, not
captured from encoder output. The spec asserts encoder output EQUALS the vector,
which is the direction that catches a symmetric encode/decode defect — a round
trip alone passes one straight through. This was demonstrated, not assumed:
swapping `reads` and `writes` in BOTH `mutation_effect_put` and
`mutation_effect_read` left every round-trip assertion green and was caught by
exactly three exact-byte assertions.

Gate: `test/01_unit/common/structural/mutation_contract_spec.spl` — 70 examples.
