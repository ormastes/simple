# Frozen Contract v1 — Identity and TagMap (ID-TAG lane)

**Date:** 2026-07-31 · **Status:** Frozen (wave 0a) · **Lane:** ID-TAG

Normative parents (these win on any conflict):

- `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`
  — §4 identity model, §5 TagMap framework, §25 source placement,
  §26 contract freeze, §27 lane ownership, §30.1/§30.2 verification.
- `doc/03_plan/platform/structural_compute/README.md` — shared lane rules.
- `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` — §10 isolation rules.

This document freezes the first two of the ten artifact groups listed in
architecture §26:

1. `EntityRef` / `EntityKey` / `SnapshotId`
2. `TagSchema` and tag encoding

The remaining eight groups are owned by other lanes and are **not** covered
here. They should follow the conventions in this document rather than inventing
their own.

---

## 1. Module placement and why

Architecture §25 specifies the ownership boundary directly:

```text
src/lib/common/structural/
    identity/
    tagmap/
    ...
```

That matches `.claude/rules/structure.md`, which reserves `src/lib/common/` for
pure functions. These are value types plus pure serializers — no I/O, no
allocation policy, no runtime family dependency — so `common` is correct and the
placement is doc-mandated rather than inferred.

Shipped files:

```text
src/lib/common/structural/wire.spl                 shared wire primitives
src/lib/common/structural/identity/__init__.spl    facade
src/lib/common/structural/identity/entity_id.spl   types + predicates
src/lib/common/structural/identity/identity_codec.spl  CPU reference codec
src/lib/common/structural/tagmap/__init__.spl      facade
src/lib/common/structural/tagmap/tag_schema.spl    types + enums
src/lib/common/structural/tagmap/tag_codec.spl     CPU reference codec

test/fixtures/structural/identity_tagmap_golden_v1.spl   golden vectors
test/fixtures/structural/identity_tagmap_golden_v1.sdn   language-neutral mirror
test/01_unit/common/structural/identity_tagmap_contract_spec.spl
```

No `FILE.md` manifest exists in `src/lib`, `src/lib/common`, or `test/fixtures`,
so no manifest entry was required. No shared export, driver, CLI, or MDSOC
binding file was touched: module resolution is path-based, so
`use std.common.structural.identity.{...}` resolves with no registry edit. This
respects the §27 shared-file rule and gpu_web_scene §10 rule 4.

---

## 2. CONVENTIONS (normative for the nine following contract lanes)

Copy these. They are deliberately minimal.

### 2.1 Module layout

```text
src/lib/common/structural/<group>/__init__.spl    explicit re-exports only
src/lib/common/structural/<group>/<group>_types.spl   value structs + enums
src/lib/common/structural/<group>/<group>_codec.spl   CPU reference codec
```

Types and codec stay in separate files so a consumer that only needs the shape
does not pull in the serializer. `__init__.spl` uses explicit
`export use ...{A, B}` — never `export use *`, which the linter flags.

### 2.2 Naming

| Thing | Convention | Example |
|---|---|---|
| Value struct | `PascalCase`, as spelled in the architecture | `EntityKey` |
| Constructor | `snake_case` of the type | `entity_key(...)` |
| Structural equality | `<type>_equal` | `entity_key_equal` |
| Unframed field writer | `<type>_put(out, v) -> [u8]` | `entity_ref_put` |
| Unframed field reader | `<type>_read(data, off) -> T` | `entity_ref_read` |
| Framed record encoder | `encode_<type>(v) -> [u8]` | `encode_entity_key` |
| Framed record decoder | `decode_<type>(data) -> <Type>Result` | `decode_entity_key` |
| Enum to wire | `<enum>_to_u8` | `tag_lifetime_to_u8` |
| Enum from wire | `<enum>_from_u8` | `tag_lifetime_from_u8` |
| Enum bound check | `<enum>_valid` | `tag_lifetime_valid` |
| Encoded size constant | `<TYPE>_LEN` | `ENTITY_KEY_LEN` |
| Schema version constant | `<GROUP>_SCHEMA_VERSION` | `TAGMAP_SCHEMA_VERSION` |

### 2.3 Serializer style

- **Little-endian, fixed width, no padding, no alignment.** Every multi-byte
  integer goes through `common/structural/wire.spl`.
- **Mask after every shift.** `(v >> 56) & 0xFF`. Simple's `>>` sign-extends, so
  an unmasked high byte of a u64 with the top bit set emits `0xff` filler.
- **Widen before shifting across 32 bits.** A parameter declared `u32` shifted
  left by 32 evaluates at 32-bit width and silently yields zero. Declare such
  parameters `u64` and mask. This was a live defect caught by the SmallSet
  golden vector during this lane's own verification.
- **Enums encode as one `u8`.** Discriminants are wire values: never renumber,
  never reuse a retired number.
- **Lists encode as `u32` count then elements.** Decoders must verify the count
  against the remaining buffer *before* allocating.
- **Every top-level record carries an 8-byte envelope:**
  `magic u32 | version u16 | reserved u16 (== 0)`. Magic is four ASCII bytes,
  first character in the low byte, distinct per record type so a mis-routed
  buffer is rejected rather than reinterpreted.
- **Decoders are total and return a result struct** with an `ok` flag, not an
  `Option` — Option lowering differs across this repo's engines. Malformed input
  never traps.
- **Unknown discriminants and version mismatches are HARD REJECTS.** Never
  coerce to a default. Two lanes silently disagreeing about a tag's meaning
  while both report success is the exact failure the freeze exists to prevent.

### 2.4 Golden vectors

- Location: `test/fixtures/structural/<group>_golden_v<N>.spl`, pure data, no
  file I/O, so a spec imports them and they behave identically in every
  execution mode.
- Mirror: a sibling `<group>_golden_v<N>.sdn` carrying the identical bytes for
  language-neutral consumers. The mirror must be verified against encoder output,
  not hand-maintained.
- Encoding: lowercase, unseparated hex of the complete framed record.
- **Derive the hex by hand from the layout, not by capturing encoder output.**
  A vector captured from the encoder cannot detect the encoder drifting; it only
  detects the encoder disagreeing with itself.
- Cover, per record shape: a zero case, an all-ones case, and an asymmetric case
  that catches byte-order errors.
- **Never edit a vector in place.** A contract change adds
  `<group>_golden_v<N+1>.spl` and keeps the old file so cross-version
  compatibility stays testable.

### 2.5 Spec requirements

A contract spec proves three separate things. Round-tripping alone is
insufficient — it passes happily when encoder and decoder drift together.

1. **Exact bytes** — encoder output equals the hand-derived golden vector.
2. **Round trip** — `decode(encode(x))` reconstructs `x` for every shape.
3. **Rejection** — truncated, cross-typed, wrong-version, wrong-reserved and
   unknown-discriminant buffers are refused.

The spec must carry an active (uncommented) `use` of the module under test, and
non-vacuity must be demonstrated with a sentinel: break the implementation,
observe the spec fail, restore.

---

## 3. Frozen layout — identity (architecture §4)

`IDENTITY_SCHEMA_VERSION = 1`

| Record | Bytes | Magic | Layout |
|---|---|---|---|
| `Hash128` | 16 | — | `hi u64` \| `lo u64` |
| `ArtifactId` | 20 | — | `content_hash Hash128` \| `schema_version u32` |
| `EntityRef` | 8 | `SREF` | `object_slot u32` \| `local_index u32` |
| `EntityKey` | 32 | `SKEY` | `artifact ArtifactId` \| `schema u32` \| `local_identity u64` |
| `SemanticEntityKey` | 44 | `SSEM` | `language u32` \| `qualified_name u32` \| `signature_hash Hash128` \| `definition_artifact ArtifactId` |
| `SourceAnchor` | 36 | `SANC` | `file ArtifactId` \| `byte_start u32` \| `byte_end u32` \| `spelling_context u32` \| `expansion_context u32` |
| `SnapshotId` | 28 | `SSNP` | `root_artifact ArtifactId` \| `epoch u64` |

`EntityRef` is exactly 64 bits of payload, as §4.1 requires for hot arrays and
GPU kernels. It embeds no raw address.

### Resolution rules (§30.1)

- `entity_key_resolvable_in(key, snapshot)` — a durable key resolves only when it
  names the same artifact **including that artifact's schema version**. A key
  produced under a different schema version of identical content is *not*
  resolvable: the node numbering it refers to may have changed meaning.
- `entity_ref_stale(ref_snapshot, current)` — strict inequality. An `EntityRef`
  is snapshot-local, so it is stale the moment the current snapshot differs at
  all. A mutation against a stale snapshot fails rather than silently modifying
  newer state (§4.4).
- `snapshot_supersedes(newer, older)` — same artifact lineage, greater epoch.

---

## 4. Frozen layout — tagmap (architecture §5)

`TAGMAP_SCHEMA_VERSION = 1`

`TagKey` is 13 bytes:
`namespace u32` | `name u32` | `value_type u8` | `cardinality u8` |
`lifetime u8` | `merge_policy u8` | `authority u8`

`TagSchema` (magic `STSC`): envelope | `version u32` | `key_count u32` |
`TagKey * key_count`. The decoder rejects a buffer whose length does not exactly
match the declared count.

`TagValue` (magic `STVL` when framed): `value_type u8` | payload.

| `TagValueType` | Disc | Payload |
|---|---|---|
| `Marker` | 0 | none |
| `Bool` | 1 | `u8`, normalised to 0/1 |
| `I64` | 2 | 8 |
| `U64` | 3 | 8 |
| `F64` | 4 | 8 — raw IEEE-754 bit pattern |
| `StringId` | 5 | 4 |
| `EntityRef` | 6 | 8 |
| `ArtifactId` | 7 | 20 |
| `SourceAnchor` | 8 | 36 |
| `SmallSet` | 9 | 8 — offset in low 32 bits, count in high 32 |

Other frozen discriminants:

- `TagLifetime`: `Snapshot` 0, `Stage` 1, `Artifact` 2, `ProfileSession` 3,
  `DiagnosticOnly` 4.
- `TagMergePolicy`: `Replace` 0, `Union` 1, `AppendStable` 2, `Max` 3, `Min` 4,
  `ErrorOnConflict` 5.
- `TagCardinality` (**provisional vocabulary**): `One` 0, `Optional` 1, `Many` 2.
- `TagAuthority` (**provisional vocabulary**): `Parser` 0, `Semantic` 1,
  `Analysis` 2, `Profile` 3, `External` 4, `Policy` 5.

---

## 5. Versioning and compatibility policy

Modelled on architecture §12.6, which requires rejecting unknown versions rather
than assuming compatibility.

```simple
struct StructuralContractCapability:
    identity_schema: u16
    tagmap_schema: u16
```

Rules:

1. **A version mismatch is a rejection, not a negotiation.** A decoder accepts
   exactly its own `*_SCHEMA_VERSION`. There is no forward-compatible "ignore
   unknown trailing bytes" path; §26 freezes contracts precisely so that two
   producers cannot disagree while both claim success.
2. **A frozen file is never edited in place** (gpu_web_scene §10 rule 3). Any
   change to a field, its order, its width, or an enum discriminant is a new
   schema version.
3. **Bump the group's `*_SCHEMA_VERSION`** for any wire-visible change. Identity
   and tagmap version independently; a tagmap change does not invalidate stored
   identity records.
4. **Enum discriminants are append-only.** New variants take the next free
   number. A retired variant's number is burned, never reused.
5. **Extending a provisional vocabulary** (`TagCardinality`, `TagAuthority`) is a
   `TAGMAP_SCHEMA_VERSION` bump, but because the slot width and surrounding
   `TagKey` offsets are already frozen, it does not disturb any other field.
6. **Each version keeps its golden-vector file**, so cross-version compatibility
   remains testable after the bump.
7. `TagSchema.version` is the *schema author's* version of a particular key set
   and is independent of `TAGMAP_SCHEMA_VERSION`, which versions the encoding.
   Both are on the wire so a reader can distinguish "I do not understand this
   format" from "I understand the format but not this key set revision".

---

## 6. Rust/C++ bridge — deliberately not shipped

Architecture §26 asks for bridge types "where needed". **No bridge code is
shipped, because no caller exists at this revision.** `tools/clang-bridge/` (§25)
is not present in the tree, and the CLANG-AST and LLVM lanes own it per §27.

Shipping an uncalled bridge would create a second definition of the wire format
that nothing exercises — the opposite of what a freeze is for. What the bridge
needs instead is already provided: §3 and §4 above give the complete byte layout,
and `identity_tagmap_golden_v1.sdn` gives the vectors to validate an independent
encoder against. The owning lane writes the bridge and validates it against those
vectors.

---

## 7. Ambiguities raised back to the architecture owner

These were **not** silently guessed. Each is flagged where it appears in code.

| # | Item | Architecture ref | Gap | Resolution taken |
|---|---|---|---|---|
| 1 | `TagCardinality` variants | §5.2 | Field is declared in `TagKey` but variants are never enumerated, unlike its three sibling enums | Wire slot frozen; provisional `One`/`Optional`/`Many`, chosen as the minimum set the §5.3 storage table distinguishes (dense scalar / sparse record / offset-count set) |
| 2 | `TagAuthority` variants | §5.2 | Same — declared, never enumerated | Wire slot frozen; provisional vocabulary mirroring the producer families implied by the §5.5 namespace policy |
| 3 | `TagValue` definition | §5.4 | Used in `TagReadPort`/`TagWritePort` signatures but never defined, yet "tag encoding" is a frozen deliverable | Defined as a flat carrier keyed by `value_type`. Flat rather than a payload-carrying enum so it stays usable as a dense parallel column (§5.3) with no per-node allocation |
| 4 | `ArtifactId` structure | §4.2 | Described in prose ("content-addressed, includes the schema version"), no struct given | `Hash128` content hash + `u32 schema_version`, the minimum satisfying the prose and the §30.1 compatibility rule |
| 5 | Scalar widths | §4 | `EntitySchemaId`, `StringId`, `LanguageId`, `ExpansionContextId` have no declared width | All frozen at `u32`. `EntityKey` cannot be encoded without them |

**Recommended resolution:** ratify items 1, 2 and 3 explicitly in §5, since nine
downstream lanes will consume them. Items 4 and 5 are low-risk and can be
ratified as-is.

---

## 8. Verification status

Run: `bin/simple test test/01_unit/common/structural/identity_tagmap_contract_spec.spl`

**42 examples, 0 failures** across six groups: identity exact-bytes (8),
identity round-trip (5), identity rejection (8), tagmap exact-bytes (3),
TagValue exact-bytes for all ten types (11), tagmap round-trip and rejection (7).

Non-vacuity was demonstrated with two sentinels, each producing precisely
targeted failures before being reverted:

1. Swapping `object_slot`/`local_index` in `entity_ref_put` → 2 failures, both
   byte-order-sensitive assertions, in two different groups.
2. Disabling the envelope version check in `wire_check_envelope` → 1 failure,
   exactly the version-rejection assertion.

See the wave report for the execution-engine caveat that applied at the time of
this run.
