# DirtyMask and dependency edge format — frozen contract v1

Artifact group 6 of architecture §26 ("DirtyMask and dependency edge format").
Owned by the INVALIDATE lane (§27: `structural/invalidation`).

Source of truth: `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`
§9.1 (dirty mask), §9.3 (dependency edges), §9.4 (InvalidationPort), §9.5
(compiler invalidation).

| Deliverable (§26) | Where |
|---|---|
| Language-neutral binary/SDN schema | this document + `test/fixtures/structural/invalidation_golden_v1.sdn` |
| Simple types | `src/lib/common/structural/invalidation/{dirty_mask,invalidation_edge}.spl` |
| Rust/C++ bridge types | none needed — see "Bridge types" below |
| CPU reference serializers | `src/lib/common/structural/invalidation/invalidation_codec.spl` |
| Golden vectors | `test/fixtures/structural/invalidation_golden_v1.{spl,sdn}` |
| Compatibility/versioning policy | "Versioning" below |

Gate: `test/01_unit/common/structural/invalidation_contract_spec.spl`.

## Conventions

Inherited unchanged from the ID-TAG lane (`common/structural/wire.spl`) and used
identically by the MAP lane:

- all integers little-endian, fixed width, **no padding, no alignment**;
- every enum is a single `u8` discriminant;
- every top-level record carries an 8-byte envelope
  `magic u32 | version u16 | reserved u16 (== 0)`;
- decoders are total — they return an `ok` flag rather than trapping;
- an unknown discriminant, a set reserved bit, or a broken structural invariant
  is a **HARD REJECT**, never a silent default;
- every invariant is enforced on **encode as well as decode**. An ill-formed
  record encodes to an empty buffer, so a producer cannot put bytes on the wire
  that no reader will accept and then blame the reader.

Magics: `SDMK` DirtyMask, `SDEP` InvalidationEdge, `SDBA` InvalidationEdgeBatch.

## DirtyMask (§9.1)

`u32` bitset, one bit per stage, in §9.1 declaration order starting at bit 0.

| Bit | Stage | Bit | Stage | Bit | Stage |
|---|---|---|---|---|---|
| 0 | Source | 7 | Optimization | 14 | IntrinsicMeasure |
| 1 | Token | 8 | Codegen | 15 | Layout |
| 2 | Parse | 9 | Link | 16 | Paint |
| 3 | SyntaxIndex | 10 | DomStructure | 17 | Composite |
| 4 | Semantic | 11 | SelectorIndex | 18 | HitTest |
| 5 | Hir | 12 | Cascade | 19 | Accessibility |
| 6 | Mir | 13 | ComputedStyle | 20 | Resource |

`DIRTY_MASK_KNOWN = 0x001fffff`. **Bits 21..31 are RESERVED and MUST be zero;
a set reserved bit is a hard reject.**

The ordering is load-bearing, not incidental: §9.1 lists the compiler pipeline
(Source..Link) then the document/render pipeline (DomStructure..Accessibility),
so a stage's bit index is monotone in the order work actually happens.

Wire: `envelope(8) | mask u32`.

The `DirtyMask` **struct is not redeclared** by this lane — it already exists in
`invalidation/contracts.spl` and is imported by six modules. This contract adds
the frozen bit vocabulary to the existing struct.

## InvalidationEdge (§9.3)

21 bytes, no padding. Field order is §9.3's declaration order.

| Offset | Size | Field |
|---|---|---|
| 0 | 8 | `producer` EntityRef |
| 8 | 8 | `consumer` EntityRef |
| 16 | 1 | `kind` u8 |
| 17 | 4 | `invalidates` u32 (DirtyMask bitset) |

`invalidates` is the set of stages that go dirty in the **consumer** when the
**producer** changes. It is both the trigger set and the effect set — that is
what §9.3 declaring one field rather than two means.

**An edge whose `invalidates` is empty is rejected.** §9.3 exists to propagate
invalidation; a zero-mask edge can never fire, so recording one is a producer
bug that would otherwise sit in the graph undetected forever. There is therefore
no all-zero InvalidationEdge on the wire.

`producer` and `consumer` are snapshot-local EntityRefs (§4.1), so an edge is
only meaningful inside its snapshot. A dependency that must survive a revision
is re-derived against EntityKey (§4.2), never stored across revisions.

### InvalidationEdgeKind

| Discriminant | Variant | §9.3 bullet |
|---|---|---|
| 0 | SymbolExport | exported symbol → dependent module semantic artifact |
| 1 | CustomProperty | CSS custom property → computed declarations that reference it |
| 2 | SelectorMatch | DOM class value → candidate selector set |
| 3 | LayoutGeometry | computed width → containing block layout |
| 4 | FontMetric | font metric → text fragments and parent intrinsic size |
| 5 | LinkRelocation | input symbol → relocation and output range |

## InvalidationEdgeBatch (§9.4)

Compressed sparse row over producers — **the MAP lane's §6.3 layout reused, not
a parallel scheme.** It shares the MAP lane's actual invariant checker
(`mapping_offsets_well_formed`); a CSR rule enforced by two functions is a CSR
rule with two meanings.

```
envelope(8) | version u32 | producer_count u32 | edge_count u32 | has_reverse u8
            | producer_offsets u32 * (producer_count + 1)
            | edges InvalidationEdge * edge_count
            | [ consumer_count u32
            |   consumer_index_count u32
            |   consumer_offsets u32 * (consumer_count + 1)
            |   consumer_edges u32 * consumer_index_count ]
```

The bracketed tail is present only when `has_reverse == 1`; any other byte in
that field is a hard reject.

Invariants:

- `producer_offsets` has `producer_count + 1` entries, starts at 0, is
  non-decreasing, and ends at `edge_count`. Edges leaving producer `n` are
  `producer_offsets[n] .. producer_offsets[n+1]`.
- `consumer_edges` holds **u32 indices into `edges`**, never duplicated edge
  bodies, so the two directions cannot disagree.
- `consumer_offsets` is a CSR over `consumer_edges`, so its terminal entry is
  `consumer_index_count`, which may be **less than** `edge_count`: an edge whose
  consumer lies outside the indexed range is legitimately not indexed.
- Every `consumer_edges` entry is `< edge_count`.

The consumer index is optional and built on demand: `derive` (§9.4) walks
producer → consumer and needs only the forward direction; `explain` (§9.4) walks
consumer → producer and is the caller that must demand it. It is built by
counting sort, which makes it deterministic — two builders that see the same
forward edges in the same order produce byte-identical arrays, which is what
lets golden vectors freeze the format at all.

A corrupt CSR does not fail loudly; it silently returns a neighbouring node's
dependencies. That is why the offset checks are re-run on decode even though
encode already enforced them.

### Width discipline

Every declared count is a `u32` that can reach 4294967295, and **every span
derived from one is computed in i64, never at 32-bit width**. At u32 width
`producer_count + 1` wraps to 0 for the maximum count and the bounds check
`(count + 1) * 4` then passes trivially against any buffer, admitting a record
whose arrays were never present. The gate pins this with a
maximum-count-on-a-short-buffer case.

## One-hop propagation

`invalidation_propagate_once` is the frozen reference semantics: an edge fires
only when the producer's dirty mask intersects the edge's `invalidates`, and
when it fires the consumer acquires exactly that whole mask — including stages
the producer never set.

Budgeted multi-hop propagation (§9.4 `propagate`) is scheduler behaviour and is
**not** part of this contract. One hop is, so that every backend agrees on what
one hop does.

## Bridge types

None required. Unlike the identity lane there is no Rust/C++ structure that
already holds these records: the dependency graph is produced and consumed
inside the structural-compute layer. The `.sdn` mirror is the language-neutral
contract for any future non-Simple validator; it carries the full framed hex of
every vector, so a foreign encoder can be checked without linking Simple.

## Versioning

- `INVALIDATION_SCHEMA_VERSION = 1`, carried in every envelope.
- **Enum discriminants and bit positions are wire values.** A discriminant or a
  bit is never reused and never renumbered. New stages take the next free bit
  (21 and up); new edge kinds take the next free discriminant (6 and up).
- Adding either requires a **version bump**, because `DIRTY_MASK_KNOWN` and the
  kind-validity bound both widen and previously-rejected buffers would start
  being accepted.
- A version mismatch is a **rejection, not a negotiation** (§12.6, §30.1).
- Reserved bits and the envelope reserved word must be zero on write and are
  rejected when non-zero on read, so a v1 reader can never silently accept a v2
  record.

## Underspecified in §9 — derivations raised for ratification

1. **`DependencyKind` variants.** §9.3 declares the field and never lists a
   variant. Frozen as exactly the six edge classes §9.3's own "Examples:" list
   distinguishes, in the order given. Derivation: those six are the only edge
   classes the section separates, and §9.5 requires SymbolExport and
   LinkRelocation to be separately identifiable (a private implementation change
   must preserve dependents' semantic artifacts while still invalidating codegen
   and linking).
2. **`DependencyEdgeBatch` shape.** §9.4 names the type in
   `record_dependencies(edges: DependencyEdgeBatch)` and never defines it.
   Frozen as CSR over producers, deliberately identical to §6.3's MappingShard
   rather than a new scheme.
3. **DirtyMask wire width.** §9.1 gives 21 flags and no width. 21 bits do not
   fit a u16, so the smallest fixed width that holds the frozen set is u32 —
   the same derivation the MAP lane used for `MappingKindSet`.
4. **Empty-mask edges.** Not addressed by §9. Frozen as rejected, on the
   grounds that §9.3's purpose is propagation and a non-firing edge is
   unobservable except as graph bloat.

## Divergences — MUST be reconciled, not yet ratified

**The layout lane's `DIRTY_*` constants are not on the canonical bits.**
`invalidation/contracts.spl` carries four shorthand constants packed at 1/2/4/8
(bits 0..3):

| Constant | Current bit | Canonical §9.1 bit |
|---|---|---|
| `DIRTY_INTRINSIC_MEASURE` | 0 | 14 |
| `DIRTY_LAYOUT` | 1 | 15 |
| `DIRTY_HIT_TEST` | 2 | 18 |
| `DIRTY_RESOURCE` | 3 | 20 |

The layout lane packed the four stages it cared about into the low bits before
the contract freeze existed. Nothing observes the difference **today**: those
constants are never serialized, and every consumer (`structural/layout`,
`gpu_web/layout`, `simple_web_render_session` and their specs) composes them
symbolically with `|` and `&` — a repository-wide grep found no numeric dirty
literal at any call site. But bit 0 currently means *IntrinsicMeasure* to the
layout lane and *Source* on the wire, so the moment any layout dirty state
reaches the wire the two readings silently disagree with no error.

This contract does **not** renumber them. Renumbering is a change to an existing
module owned by another lane, and it could not be verified in this wave (see the
note in the delivery report on stdlib module resolution). The gate pins the four
constants at their current values so the packing cannot drift while the
reconciliation is ratified.

**Recommended resolution:** redefine the four constants to the canonical bits
(16384 / 32768 / 262144 / 1048576). Expected to be behaviour-preserving given
the symbolic-only usage, but it must be landed with the layout and gpu_web specs
green.

## Naming divergence from §9.3

§9.3 spells the records `DependencyEdge` / `DependencyKind`. Both bare names are
already taken in this tree by unrelated types:

- `src/compiler/40.mono/monomorphize/note_sdn.spl` — `DependencyKind`
  (TypeParam / FieldType / InnerType / MethodDep) and `DependencyEdge`
  (`from_inst` / `to_inst` text pair), for monomorphization notes;
- `src/compiler/90.tools/size/dependency_audit.spl` — `DependencyEdge`
  (`from_crate` / `to_crate`), for the crate-size audit.

Same name, different meaning. The interpreter resolves struct names through a
global registry, so declaring a third `DependencyEdge` risks silently rebinding
those call sites rather than colliding loudly. Frozen here as
`InvalidationEdge` / `InvalidationEdgeKind` / `InvalidationEdgeBatch`, leaving
the existing types untouched — the same resolution the EXEC lane used when
§21's `ExecutionProfile` collided with an existing measured-cost record. **The
§9.3 field names are preserved exactly; only the type spellings differ.** Raised
for ratification.
