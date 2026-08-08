# Frozen mapping contract v1 — MappingKind and the compressed mapping format

Status: **FROZEN** (wave 0b of the contract-freeze phase)

Architecture:
`doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`
§6 (MappingGraph and provenance), §26 contract freeze, §27 lane ownership
(MAP owns `structural/mapping`).

This document is the normative statement of artifact group 3 of §26:
*"MappingKind and compressed mapping format"*. It is the third and fourth of
the eleven versioned artifacts to freeze, after the ID-TAG lane's
`identity_tagmap_contract_v1.md` (wave 0a), whose conventions it inherits
unchanged.

## 1. Deliverables

| §26 deliverable | Where |
|---|---|
| Language-neutral binary/SDN schema | §3–§5 below, mirrored in `test/fixtures/structural/mapping_golden_v1.sdn` |
| Simple types | `src/lib/common/structural/mapping/mapping_edge.spl` |
| Rust/C++ bridge types | Not shipped — see §9 |
| CPU reference serializers/deserializers | `src/lib/common/structural/mapping/mapping_codec.spl` |
| Golden vectors | `test/fixtures/structural/mapping_golden_v1.spl` (+ `.sdn`) |
| Compatibility/versioning policy | §8 |

Verification gate: `test/01_unit/common/structural/mapping_contract_spec.spl`.

## 2. Inherited conventions

Byte-level conventions are **not** restated here. They are frozen in
`src/lib/common/structural/wire.spl` and stated normatively in
`identity_tagmap_contract_v1.md`:

- all integers little-endian, fixed width, **no padding, no alignment**;
- every enum encodes as a single `u8` discriminant;
- every top-level record carries the 8-byte envelope
  `magic u32 | version u16 | reserved u16 (== 0)`;
- decoders are total (they return an `ok` flag, they do not trap);
- **an unknown enum discriminant is a HARD REJECT, never a silent default**;
  this contract extends the rule to *any set reserved bit*, for the same
  reason.

`MAPPING_SCHEMA_VERSION = 1`. Magics: `SMED` (MappingEdge), `SMKS`
(MappingKindSet), `SMSH` (MappingShard).

## 3. MappingKind

The 17 variants of §6.2, in declaration order, at discriminants 0..16:

| # | Variant | # | Variant | # | Variant |
|---|---|---|---|---|---|
| 0 | ParsedFrom | 6 | InlinedFrom | 12 | CascadesInto |
| 1 | ExpandedFrom | 7 | WovenFrom | 13 | LayoutOf |
| 2 | DesugaredFrom | 8 | OptimizedFrom | 14 | PaintOf |
| 3 | ResolvedFrom | 9 | GeneratedFrom | 15 | HitRegionOf |
| 4 | LoweredFrom | 10 | LinkedFrom | 16 | InvalidatedBy |
| 5 | ClonedFrom | 11 | Styles | | |

**The enum is not redeclared.** It already existed in this lane's
`mapping/contracts.spl` with exactly these variants in exactly this order, and
is already imported by `structural/layout` and by
`src/compiler/00.common/structural_contracts/sidecars.spl`. `mapping_edge.spl`
imports that declaration and adds the wire mapping to it. Two declarations of
one wire enum is precisely how two lanes come to disagree about a discriminant
while both report success.

`OriginPolicy` (§6.5) is likewise fully enumerated by the architecture and is
frozen as given at 0..5: PreserveOneToOne, Split, Merge, Clone, Synthesize,
DiscardWithReason. It is declared per transformation, not per edge, so it is
not a `MappingEdge` field; it is frozen here because it governs which edges a
pass may emit and every lane must agree on its discriminants.

## 4. MappingEdge — 27 bytes, no padding

Field order on the wire is the declaration order given in §6.2.

| Offset | Width | Field |
|---|---|---|
| 0 | 8 | `from` — EntityRef |
| 8 | 8 | `to` — EntityRef |
| 16 | 1 | `kind` — MappingKind discriminant |
| 17 | 4 | `transform` — TransformInstanceId (u32, **derived**, §7) |
| 21 | 4 | `flags` — MappingFlags (u32 bitfield, **derived**, §7) |
| 25 | 2 | `weight_milli` — u16 |

`weight_milli` is thousandths: 1000 is a whole share. §6.2's own worked example
attributes 600/400 across two inputs of a merged instruction.

`from` and `to` are snapshot-local EntityRefs (§4.1), so an edge is meaningful
only inside its shard's snapshot. Durable provenance is obtained by resolving
through `EntityKey` (§4.2), never by storing edges across revisions.

## 5. MappingShard — the compressed mapping format

§6.3 states the storage form as four arrays — `from_offsets[]`, `from_edges[]`,
`reverse_offsets[]` (*"built only when demanded"*), `reverse_edges[]`. That is
compressed sparse row (CSR). Frozen layout:

```text
envelope(8)                  magic "SMSH", version 1
version              u32
node_count           u32     = N
edge_count           u32     = E
has_reverse          u8      0 or 1 ONLY
from_offsets         u32 * (N + 1)
edges                MappingEdge * E        (27 bytes each)
--- present only when has_reverse == 1 ---
reverse_node_count   u32     = M
reverse_index_count  u32     = R
reverse_offsets      u32 * (M + 1)
reverse_edges        u32 * R                indices into `edges`
```

Offset arrays carry no length prefix: their length is already implied by the
node count, and a second count would be a field two lanes could disagree about.

### 5.1 Structural invariants (enforced identically on encode and decode)

- `from_offsets` has `N + 1` entries, starts at 0, is non-decreasing, and ends
  at `E`. Edges for node `n` are `from_offsets[n] .. from_offsets[n+1]`.
- `reverse_offsets` obeys the same rule against `R`.
- every `reverse_edges[i] < E`.
- `R <= E`. `R < E` is legal: a lazily built *partial* reverse index does not
  cover targets outside the reverse node range.
- `has_reverse == 0` implies both reverse arrays are empty.
- no trailing bytes.

`encode_mapping_shard` returns an **empty buffer** for a shard that violates
these, rather than emitting bytes no decoder will accept. A producer must not
be able to put a corrupt CSR on the wire.

These checks matter more here than anywhere in wave 0a. A corrupted offset
array does not fail loudly — it silently returns a *neighbouring node's*
provenance. Provenance that is wrong-but-plausible is exactly what §6.5 forbids
("a pass cannot silently drop origins").

### 5.2 reverse_edges holds indices, not edges

§6.3 calls the structure *"the reverse index"* and says a stage "can emit
forward edges cheaply and construct the reverse index lazily". An index that
duplicated every 27-byte edge body would not be cheap, and the two copies could
disagree. `reverse_edges` is therefore a `u32` index into the forward edge
list.

`mapping_build_reverse` is a counting sort over `to.local_index`. It is
deterministic by construction: two builders that see the same forward edges in
the same order produce byte-identical reverse arrays. That determinism is what
lets a golden vector freeze the format at all.

## 6. Golden vectors

`test/fixtures/structural/mapping_golden_v1.spl`, mirrored byte-for-byte in
`mapping_golden_v1.sdn` for language-neutral consumers. Every hex string was
derived **by hand** from the layout above, not captured from encoder output;
that is what makes them an oracle. Ten vectors: four edges (zero, fully
asymmetric, all-ones at the maximum discriminant, synthesized-and-discarded),
three kind-sets (empty, all 17 bits, `{LayoutOf, PaintOf}`), three shards
(empty, forward-only, forward + reverse).

The convention is wave 0a's and is unchanged: lowercase unseparated hex, pure
data with no file I/O, zero and all-ones edge cases, and **a vector is never
edited in place** — a contract change adds `mapping_golden_v<N+1>.spl` and
keeps the old file so cross-version compatibility stays testable.

## 7. Underspecified in §6 — raised for ratification

Wave 0a's rule applies: where the architecture underspecifies, freeze the wire
**slot**, pick the minimum vocabulary the surrounding sections actually
distinguish, mark it, and report it back. Nothing below was invented for
convenience; each row cites the text that forces it.

| # | Item | §ref | Gap | Frozen as | Derived from |
|---|---|---|---|---|---|
| 1 | `MappingKindSet` | §6.4 | Used as `kind_mask` in `forward`/`reverse`; never defined | `u32` bitset, bit *i* = MappingKind discriminant *i*; bits 17..31 reserved, must be zero | The parameter is named *mask*, and §6.2 enumerates 17 kinds. 17 bits do not fit a `u16`, so `u32` is the smallest fixed width that holds the frozen enum |
| 2 | `TransformInstanceId` | §6.2 | Used as a `MappingEdge` field; **occurs exactly once in the entire repository**, at that declaration | `u32` | The scalar-width rule the ID-TAG lane already ratified in `ae87d52fbdf`: undeclared identity scalars are `u32` |
| 3 | `MappingFlags` | §6.2 | Declared as a field; **not one flag is ever named** | `u32` bitfield with three bits; bits 3..31 reserved, must be zero | Each bit cites a sentence — see below |
| 4 | `reverse_edges` element type | §6.3 | Array named, element type never given | `u32` index into the forward edge list | §6.3 calls it "the reverse **index**" and requires it be cheap to build lazily |
| 5 | CSR invariants | §6.3 | Four arrays named, no well-formedness rule stated | §5.1 above | A CSR is undecodable without them; without the terminator rule `N`+1 vs `N` entries is ambiguous |
| 6 | Missing `weight_milli` | §6.2 | Weight is "optional" with no representation for *absent* | `WEIGHT_VALID` bit; absent weight reads as 1000 milli | "Optional" is unrepresentable otherwise: 0 attribution and no attribution would be identical bytes |

### MappingFlags bit derivation

| Bit | Name | Sentence that forces it |
|---|---|---|
| 0 (1) | `WEIGHT_VALID` | §6.2 "`weight_milli` is optional diagnostic attribution". Without a bit, an edge attributing 0/1000 and an edge supplying no attribution encode identically |
| 1 (2) | `SYNTHETIC` | §6.5 `Synthesize`, and §6.1 "or synthesize entities" — the target has no true source origin. §6.1 opens by arguing a single source pointer is insufficient *because* entities are synthesized |
| 2 (4) | `DISCARDED` | §6.5 `DiscardWithReason` plus "A pass cannot silently drop origins." A dropped origin not recorded as an edge *is* the silent drop the rule forbids |

### Deliberately NOT frozen here

`MappingShardRef` (§6.4 `finish()`, and a field of `StageReceipt`,
`VerificationReceipt`, and six other records), `SourceOriginSet` (§6.4
`trace_to_source`) and `EntitySetView` (§6.4, and §5 `TagIndexPort`) are
**handle and view types, not the compressed mapping format**. `EntitySetView`
in particular is shared with the tag and query groups. Freezing them from
inside the MAP lane would pre-empt the StageReceipt and QueryIR artifact
groups. They are listed here so the gap is tracked rather than forgotten.

## 8. Compatibility and versioning policy

1. **Discriminants are wire values.** A `MappingKind` or `OriginPolicy`
   discriminant is never reused and never renumbered. New variants take the
   next free number.
2. **Adding an 18th MappingKind is a breaking change to `MappingKindSet`.**
   `MAPPING_KIND_SET_ALL` is pinned at `0x0001FFFF` by a golden vector, and bit
   17 is currently a hard-reject reserved bit. Adding a kind requires a schema
   version bump.
3. **Reserved bits are hard-rejected, not ignored.** A reader that masked off an
   unknown `MappingFlags` bit would answer a provenance query while silently
   discarding what the producer meant. A reader that masked off an unknown
   `MappingKindSet` bit would answer a `forward(entity, kind_mask)` query about
   kinds it does not know, and report success.
4. **Version mismatch is rejection, not negotiation.** `wire_check_envelope`
   requires the exact frozen version. There is no forward-compatible read path
   in v1.
5. **Field widths, field order and record lengths are frozen.** `MappingEdge`
   is 27 bytes. Any change is a `MAPPING_SCHEMA_VERSION` bump plus a new golden
   vector file; never an in-place edit of v1.
6. **A change to any DERIVED item in §7 that ratification overturns is still a
   version bump**, even though the architecture never stated the original value.
   The golden vectors are the contract, not the doc's silence.

## 9. Why no Rust/C++ bridge

No Rust or C++ caller exists at this revision, and §26 requires bridge types
only "where needed". The byte layout in §4–§5, the discriminant tables in §3,
and the language-neutral `.sdn` golden vectors are sufficient for the owning
CLANG-AST/LLVM lane to build and validate one when a caller appears. Shipping
an uncalled bridge now would freeze a second copy of the layout that nothing
tests.

## 10. Verification status

`bin/simple test` is **not usable at this revision** — the deployed
self-hosted binary at `bin/release/x86_64-unknown-linux-gnu/simple` is a
bootstrap-stage CLI with no `test` subcommand (`error: unknown command 'test'`).
Wave 0a's 42 examples reproduce through the Rust seed, which is the route used
here:

```text
src/compiler_rust/target/release/simple test \
    test/01_unit/common/structural/mapping_contract_spec.spl
```

**52 examples, 0 failures** across eleven groups: MappingKind discriminants (4),
OriginPolicy discriminants (2), MappingEdge exact bytes (5), MappingEdge round
trip and rejection (6), MappingKindSet (6), MappingShard exact bytes (3),
MappingShard round trip (3), CSR invariants (8), MappingShard rejection (7),
MappingReadPort semantics (6), MappingFlags vocabulary (2).

Wave 0a's `identity_tagmap_contract_spec.spl` still reports 42 examples, 0
failures on the same binary, so this lane regressed nothing it depends on.

### Non-vacuity

The spec was proved to exercise the codec by injecting a targeted defect: the
`transform` and `flags` fields were swapped in **both** `mapping_edge_put` and
`mapping_edge_read`. The run went to **52 total, 46 passed, 6 failed**, exit 1.

The instructive part is *which* tests caught it. The round-trip group stayed
**green** — the swap is symmetric, so `decode(encode(x)) == x` still held. Only
the exact-byte assertions failed, reporting e.g.

```text
expected 534d4544...0401000000443322115802
to equal 534d4544...040444332211010000005802
```

This is the wave 0a lesson reproduced live: a round-trip test alone passes
happily while encoder and decoder drift together, and the hand-derived golden
vector is the only thing that actually freezes the format. Reverting the swap
restored 52/52.
