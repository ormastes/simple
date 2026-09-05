# QueryIR contract v1 — frozen

Artifact group 4 of architecture §26 ("QueryIR bytecode and capture format"),
plus `EntitySetView`, which §6.4 explicitly deferred to this lane. Owner: QUERY
lane (§27). Source of truth for the bytes:
`src/lib/common/structural/query/`.

Architecture:
`doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`
§7 (QueryIR), §26 (contract freeze), §27 (lane ownership).

## Conventions

Inherited unchanged from the ID-TAG lane (wave 0a,
`identity_tagmap_contract_v1.md`) and the MAP lane (wave 0b,
`mapping_contract_v1.md`):

- all integers little-endian, fixed width, no padding, no alignment;
- every enum is a u8 discriminant; discriminants are wire values, never reused
  and never renumbered;
- every top-level record carries the 8-byte envelope
  `magic u32 | version u16 | reserved u16 (== 0)`;
- decoders are total and return an `ok` flag; an unknown enum discriminant, a
  set reserved bit, a non-zero reserved byte or a trailing byte is a **hard
  reject**, never a silent default;
- undeclared scalars are fixed-width unsigned little-endian, writers mask to
  width.

Magic values: `SQOP` (QueryOp), `SQCP` (CaptureSlot), `SQSV` (EntitySetView),
`SQPG` (QueryProgram). Schema version 1.

## Types frozen here

| Type | Section | Status |
|---|---|---|
| `QueryDialect` | §7.2 | frozen as given, 9 variants, 0..8 |
| `QueryOpKind` | §7.3 | frozen as given, 22 variants, 0..21 |
| `QueryOp` | §7.4 | derived word, 18 bytes |
| `CaptureSlot` / capture schema | §7.4, §7.5 | derived, 6 bytes per slot |
| `CaptureKind` | — | derived, 2 variants |
| `QueryProgram` | §7.4 | frozen field order, arenas inlined |
| `QueryDeterminism` | §7.4 | derived, 3 monotone levels |
| `TagIndexSet` | §5.6, §7.4 | wire slot only, u32 bitset |
| `EntitySetView` | §5.4, §6.4, §7.5 | derived, 13 bytes |
| `EntitySetOrder` | — | derived, 3 variants |

Types deliberately **not** redeclared: `MappingKind` / `MappingKindSet` (MAP
lane), `EntityRef` / `EntityKey` / `SnapshotId` / `ArtifactId` (ID-TAG lane),
`ExecutionProfile` (EXEC lane, already in `structural/execution`). Two
declarations of one wire type is how two lanes come to disagree about a
discriminant while both report success.

## Layouts

```text
QueryOp        18  kind u8 | reserved u8 (==0) | input_a u32 | input_b u32
                   | operand u32 | constant u32

CaptureSlot     6  name u32 | kind u8 | reserved u8 (==0)

EntitySetView  13  object_slot u32 | offset u32 | count u32 | order u8

QueryProgram       envelope(8)
                   | dialect u8 | schema_version u32 | determinism u8
                   | index_requirements u32
                   | op_count u32 | const_count u32 | capture_count u32
                   | ops       QueryOp     * op_count
                   | constants u64         * const_count
                   | captures  CaptureSlot * capture_count
```

The three counts sit together ahead of all three runs so a decoder can bound
every variable region before allocating for any of them — the ordering rule wave
0b used for the mapping shard.

`0xFFFFFFFF` is the single absent-slot sentinel for `input_a`, `input_b`,
`operand` and `constant`. A separate presence bitfield would be a second field
two producers could disagree with the first about, and §7.4's representation is
an SoA bytecode, which has no room for optionality other than a reserved value.

## Program structural rules

`query_program_valid` is the whole rule; `encode_query_program` refuses to emit
a program that fails it (it returns an empty buffer) and `decode_query_program`
re-runs it after parsing, so the accepted set is exactly the emitted set.

1. The op arena is non-empty. A program with no ops has no result set, and §7.5
   `execute` always returns one.
2. `ops[0]` is a seed (`SeedAll`/`SeedKind`/`SeedTag`/`SeedTagValue`). Seeds at
   later indices are legal — §7.7's CSS compilation seeds two sets and
   intersects them.
3. A seed carries no input; every other op carries `input_a`; only `Intersect`,
   `Union` and `Difference` carry `input_b`. `NegateWithinUniverse` is unary:
   its second operand is the request's `universe`, not another op.
4. Every input names a **strictly earlier** op. This is what keeps the arena a
   straight-line program rather than a graph and makes evaluation order
   backend-independent (§30.4). A forward or self reference does not fail
   loudly — it evaluates a different query than the one that compiled.
5. A `Capture` op's `operand` is an index into the capture schema; a
   `constant` is an index into the constant arena, or the absent sentinel.
6. Capture slot names are unique. A duplicated name would let a consumer reading
   by name silently get whichever slot the arena laid down first.
7. `index_requirements` has no reserved bit set; `dialect` and `determinism` are
   known discriminants.

## Underspecified in §7 — derivations raised for ratification

Each of these freezes a wire slot the architecture declares but never defines.
The rule applied was: do not guess a vocabulary; take the minimum the
surrounding sections actually distinguish, and cite the sentence.

| Item | Where declared | Derivation |
|---|---|---|
| `QueryDeterminism` | §7.4 field, no definition anywhere | u8, 3 monotone levels. `SetDeterministic(0)` from §7.1 "deterministic set algebra" — membership reproducible, order not, which is what a GPU set op yields before §7.3's separate `StableSort`. `OrderDeterministic(1)` from §30.4 "identical stable entity ... order". `CaptureDeterministic(2)` from §30.4's same sentence naming "entity/capture order" separately, and §3093 "for each capture(join), stable source order". Monotone (an ordered u8, not a bitset) because §21.4's no-silent-fallback rule needs a `>=` test of a backend's guarantee against a program's requirement. |
| `QueryOp` fields | §7.4 says only "SoA bytecode" | A uniform fixed-width word is what makes SoA possible; one word covers all 22 opcodes with no per-opcode tail. `operand` holds the inline immediates §7.3's ops need (kind id, depth bound, capture slot, limit count); `constant` indexes §7.4's declared `QueryConstantArena` for anything wider (TagKeyId, TagValue payload, a MappingKindSet mask for `TraverseMapping`, an interned name, a source-range bound). |
| `QueryOp.reserved` | — | §7.3 gives no evidence for any per-op flag, so rather than invent one the byte is frozen as reserved and a non-zero value is hard-rejected. A future flag is a version bump, not a silent reinterpretation. |
| `QueryConstantArena` element type | §7.4 names the arena, never its element | u64. Every constant §7.3's ops can reference fits in 64 bits (TagKeyId; §5.4's `TagValue.num` is already u64; §6.4's MappingKindSet is u32; interned names u32; §4.3 source anchors use u32 byte offsets), and a uniform element width is what keeps the arena index-addressable. |
| `CaptureKind` | §7.4/§7.5 name `CaptureSchema`/`CaptureArena`, never defined | 2 variants. `Entity(0)` from §7.6 `Capture(join_point)` and §7.8 "return canonical `EntityKey` captures"; `EntitySet(1)` because §7.3's `Capture` operates on an entity SET and §3093 iterates "for each capture(join)". No third kind invented: §7.7's specificity is a property of a compiled selector, not a capture. |
| `CaptureSlot.name` width | — | u32 interned string id, the same width and the same string table as §5.2's already-frozen `TagKey.namespace` / `TagKey.name`. |
| `TagIndexSet` | §5.6 `TagDemand.required_indexes`, §7.4 `index_requirements`; never defined | **Wire slot only.** u32 bitset, same shape and same reasoning as §6.4's ratified `MappingKindSet`. Bit *i* is storage representation *i* of §5.3's five-row table in table order: DenseMarker(0), DenseScalar(1), SparseRecords(2), InvertedQuery(3), SmallSet(4). §5.3 is the only place the document enumerates index shapes. Bits 5..31 reserved, must be zero. **This type sits on the §5 / ID-TAG side of the boundary** — the QUERY lane freezes only the width, the bit meaning and the reserved rule; naming the eventual `TagIndexKind` enum belongs to ID-TAG. |
| `EntitySetView` | §5.4, §6.4, §7.5; §6.4 explicitly deferred it to this group | 13 bytes: `object_slot u32` (same field, width and meaning as §4.1's `EntityRef.object_slot`; the Object VM descriptor carries the generation/schema/epoch/residency that §4.1 says a reference is only valid under), `offset u32`, `count u32`, `order u8`. It does **not** repeat a `SnapshotId` — §7.5's `QueryRequest` already carries one and a duplicated epoch is a field two sides can disagree about. |
| `EntitySetOrder` | — | 3 variants, NOT monotone, so never compared with `>=`. `Unordered(0)` §7.1; `EntityRefOrder(1)` — ascending `(object_slot, local_index)`, the order §4.1's hot arrays and §6.3's CSR rows already store, free from a scan; `StableSourceOrder(2)` §3093 / §30.4, what `StableSort` produces and what a receipt hashes. A view whose order is unknown cannot be fed to `Limit` and cannot be compared against another backend's output, which is why the field must exist at all. |
| Domain extension opcodes | §7.3 lists compiler/AOP/CSS/linker/layout extensions | **Not** folded into `QueryOpKind`. §7.1 is explicit that domains share "a common QueryIR plus domain-specific operations"; folding CSS pseudo-classes and linker relocation targets into the core opcode space would make every dialect's additions a breaking change to every other dialect. The extension space is the discriminant range above `QUERY_OP_KIND_MAX`, allocated by a future version bump. |

### Settled, not deferred: EntitySetView vs StageReceipt

§6.4 flagged three types as open and noted `EntitySetView` "is shared with the
tag and query groups", warning that freezing it from the mapping group "would
pre-empt the StageReceipt and QueryIR artifact groups". Checked against §21.3:
`StageReceipt`'s 13 fields are `stage`, `backend`, `mode`, `input_root`,
`output_root`, `item_count_in`, `item_count_out`, `bytes_read`,
`bytes_written`, `fallback_count`, `malformed_count`, `overflow_flags`,
`elapsed_us`, `deterministic_hash` — **none is an entity-set view**. The type
§6.4 flagged as StageReceipt-shared is `MappingShardRef`, which stays open. So
freezing `EntitySetView` here does not pre-empt the concurrent StageReceipt
lane.

Still open after this wave, unchanged: `MappingShardRef`, `SourceOriginSet`.
Also still handle/runtime types outside the wire scope and not frozen here:
`QueryProgramRef`, `QuerySource`, `QueryPlanExplanation`, `QueryParamBlock`,
`EntitySetArena`, `CaptureArena`, `DiagnosticArena`.

## Compatibility and versioning policy

Same policy as waves 0a/0b:

- `QUERY_SCHEMA_VERSION = 1`. A decoder rejects any version it does not equal;
  a version mismatch is a rejection, not a negotiation (§12.6).
- Enum discriminants are wire values. New variants take the next free number;
  a discriminant is never reused or renumbered.
- Adding a 10th `QueryDialect`, a 23rd `QueryOpKind`, a 3rd `CaptureKind`, a
  4th `QueryDeterminism` level or a 6th `TagIndexSet` bit is a **breaking**
  change requiring a version bump, because the golden vectors pin the maximum
  discriminant and the reserved-bit masks.
- Reserved bits and reserved bytes must be zero and are hard-rejected when set.
  This is what reserves them for a future version instead of letting an old
  reader silently misinterpret a new writer.
- The record lengths (`QUERY_OP_LEN = 18`, `CAPTURE_SLOT_LEN = 6`,
  `ENTITY_SET_VIEW_LEN = 13`, `QUERY_PROGRAM_HEADER_LEN = 22`) are part of the
  contract; changing one is a version bump.

## Golden vectors

`test/fixtures/structural/query_golden_v1.spl` (Simple) and
`test/fixtures/structural/query_golden_v1.sdn` (language-neutral mirror, for a
Rust/C++ bridge or an external validator).

Every hex string was derived **by hand from the layout tables above**, not
captured from encoder output. The spec asserts encoder output EQUALS the vector,
which is the direction that catches a symmetric encode/decode defect — a round
trip alone passes one straight through.

Gate: `test/01_unit/common/structural/query_contract_spec.spl`.
