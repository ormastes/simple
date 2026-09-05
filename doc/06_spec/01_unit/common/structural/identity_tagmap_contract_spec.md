# Identity Tagmap Contract Specification

> Tests covering identity contract v1 — exact bytes, identity contract v1 — round trip, identity contract v1 — rejection rules (arch 30.1), tagmap contract v1 — exact bytes, tagmap contract v1 — TagValue exact bytes, all ten types, tagmap contract v1 — round trip and rejection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Identity Tagmap Contract Specification

## Scenarios

### identity contract v1 — exact bytes

#### encodes EntityRef to the frozen 8-byte body, zero case

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes EntityRef to the frozen 8-byte body, zero case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes EntityRef to the frozen 8-byte body, zero case")
expect(wire_to_hex(encode_entity_ref(entity_ref(0, 0))))
    .to_equal(GOLDEN_ENTITY_REF_ZERO)
```

</details>

#### encodes EntityRef all-ones without sign extension

- encodes EntityRef all-ones without sign extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes EntityRef all-ones without sign extension")
expect(wire_to_hex(encode_entity_ref(entity_ref(0xFFFFFFFF, 0xFFFFFFFF))))
    .to_equal(GOLDEN_ENTITY_REF_MAX)
```

</details>

#### encodes EntityRef little-endian in field order

- encodes EntityRef little-endian in field order


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes EntityRef little-endian in field order")
expect(wire_to_hex(encode_entity_ref(entity_ref(0x01020304, 0x05060708))))
    .to_equal(GOLDEN_ENTITY_REF_ASYM)
```

</details>

#### keeps EntityRef exactly 64 bits of payload

- keeps EntityRef exactly 64 bits of payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("keeps EntityRef exactly 64 bits of payload")
expect(encode_entity_ref(entity_ref(1, 2)).len() - 8)
    .to_equal(ENTITY_REF_LEN)
```

</details>

#### encodes EntityKey to the frozen layout

- encodes EntityKey to the frozen layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes EntityKey to the frozen layout")
expect(wire_to_hex(encode_entity_key(entity_key(golden_artifact(), 3, 42))))
    .to_equal(GOLDEN_ENTITY_KEY_BASIC)
```

</details>

#### encodes SnapshotId to the frozen layout

- encodes SnapshotId to the frozen layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes SnapshotId to the frozen layout")
expect(wire_to_hex(encode_snapshot_id(snapshot_id(golden_artifact(), 9))))
    .to_equal(GOLDEN_SNAPSHOT_ID_BASIC)
```

</details>

#### encodes SemanticEntityKey to the frozen layout

- encodes SemanticEntityKey to the frozen layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes SemanticEntityKey to the frozen layout")
val k = semantic_entity_key(1, 2, hash128(0xaaaa, 0xbbbb), golden_artifact())
expect(wire_to_hex(encode_semantic_entity_key(k)))
    .to_equal(GOLDEN_SEMANTIC_KEY_BASIC)
```

</details>

#### encodes SourceAnchor with both spelling and expansion contexts

- encodes SourceAnchor with both spelling and expansion contexts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes SourceAnchor with both spelling and expansion contexts")
val a = source_anchor(golden_artifact(), 100, 200, 5, 6)
expect(wire_to_hex(encode_source_anchor(a)))
    .to_equal(GOLDEN_SOURCE_ANCHOR_BASIC)
```

</details>

### identity contract v1 — round trip

#### round-trips EntityRef including the all-ones case

- round-trips EntityRef including the all-ones case
   - Expected: d.ok is true
   - Expected: entity_ref_equal(d.value, r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips EntityRef including the all-ones case")
val r = entity_ref(0xFFFFFFFF, 0xFFFFFFFF)
val d = decode_entity_ref(encode_entity_ref(r))
expect(d.ok).to_equal(true)
expect(entity_ref_equal(d.value, r)).to_equal(true)
```

</details>

#### round-trips EntityKey including a u64 local_identity above 2^63

- round-trips EntityKey including a u64 local_identity above 2^63
   - Expected: d.ok is true
   - Expected: entity_key_equal(d.value, k) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips EntityKey including a u64 local_identity above 2^63")
val k = entity_key(golden_artifact(), 3, 0xFFFFFFFFFFFFFFFF)
val d = decode_entity_key(encode_entity_key(k))
expect(d.ok).to_equal(true)
expect(entity_key_equal(d.value, k)).to_equal(true)
```

</details>

#### round-trips SnapshotId

- round-trips SnapshotId
   - Expected: d.ok is true
   - Expected: snapshot_id_equal(d.value, s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips SnapshotId")
val s = snapshot_id(golden_artifact(), 9)
val d = decode_snapshot_id(encode_snapshot_id(s))
expect(d.ok).to_equal(true)
expect(snapshot_id_equal(d.value, s)).to_equal(true)
```

</details>

#### round-trips SemanticEntityKey

- round-trips SemanticEntityKey
   - Expected: d.ok is true
   - Expected: semantic_entity_key_equal(d.value, k) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips SemanticEntityKey")
val k = semantic_entity_key(1, 2, hash128(0xaaaa, 0xbbbb), golden_artifact())
val d = decode_semantic_entity_key(encode_semantic_entity_key(k))
expect(d.ok).to_equal(true)
expect(semantic_entity_key_equal(d.value, k)).to_equal(true)
```

</details>

#### round-trips SourceAnchor

- round-trips SourceAnchor
   - Expected: d.ok is true
   - Expected: source_anchor_equal(d.value, a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips SourceAnchor")
val a = source_anchor(golden_artifact(), 100, 200, 5, 6)
val d = decode_source_anchor(encode_source_anchor(a))
expect(d.ok).to_equal(true)
expect(source_anchor_equal(d.value, a)).to_equal(true)
```

</details>

### identity contract v1 — rejection rules (arch 30.1)

#### refuses a buffer of the wrong record type

- refuses a buffer of the wrong record type
   - Expected: decode_snapshot_id(key_bytes).ok is false
   - Expected: decode_entity_ref(key_bytes).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("refuses a buffer of the wrong record type")
val key_bytes = encode_entity_key(entity_key(golden_artifact(), 3, 42))
expect(decode_snapshot_id(key_bytes).ok).to_equal(false)
expect(decode_entity_ref(key_bytes).ok).to_equal(false)
```

</details>

#### refuses a truncated record

- refuses a truncated record
   - Expected: decode_entity_key(short).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("refuses a truncated record")
val full = encode_entity_key(entity_key(golden_artifact(), 3, 42))
var short: [u8] = []
var i = 0
while i < full.len() - 1:
    short.push(full[i])
    i = i + 1
expect(decode_entity_key(short).ok).to_equal(false)
```

</details>

#### refuses an empty buffer

- refuses an empty buffer
   - Expected: decode_entity_ref(empty).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("refuses an empty buffer")
val empty: [u8] = []
expect(decode_entity_ref(empty).ok).to_equal(false)
```

</details>

#### refuses a record whose schema version is not the frozen one

- refuses a record whose schema version is not the frozen one
   - Expected: decode_entity_ref(b).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("refuses a record whose schema version is not the frozen one")
var b = encode_entity_ref(entity_ref(1, 2))
b[4] = IDENTITY_SCHEMA_VERSION + 1
expect(decode_entity_ref(b).ok).to_equal(false)
```

</details>

#### refuses a record whose reserved envelope bytes are not zero

- refuses a record whose reserved envelope bytes are not zero
   - Expected: decode_entity_ref(b).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("refuses a record whose reserved envelope bytes are not zero")
var b = encode_entity_ref(entity_ref(1, 2))
b[6] = 1
expect(decode_entity_ref(b).ok).to_equal(false)
```

</details>

#### treats a durable key as resolvable only in its own artifact

- treats a durable key as resolvable only in its own artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("treats a durable key as resolvable only in its own artifact")
val snap = snapshot_id(golden_artifact(), 9)
val other = snapshot_id(artifact_id(hash128(1, 2), 7), 9)
expect(entity_key_resolvable_in(entity_key(golden_artifact(), 3, 42), snap))
    .to_equal(true)
expect(entity_key_resolvable_in(entity_key(golden_artifact(), 3, 42), other))
    .to_equal(false)
```

</details>

#### treats a key from a different artifact schema version as unresolvable

- treats a key from a different artifact schema version as unresolvable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("treats a key from a different artifact schema version as unresolvable")
val snap = snapshot_id(golden_artifact(), 9)
val restamped = artifact_id(hash128(0x1122334455667788, 0x99aabbccddeeff00), 8)
expect(entity_key_resolvable_in(entity_key(restamped, 3, 42), snap))
    .to_equal(false)
```

</details>

#### reports an EntityRef minted against another snapshot as stale

- reports an EntityRef minted against another snapshot as stale
   - Expected: entity_ref_stale(a, a) is false
   - Expected: entity_ref_stale(a, b) is true
   - Expected: snapshot_supersedes(b, a) is true
   - Expected: snapshot_supersedes(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("reports an EntityRef minted against another snapshot as stale")
val a = snapshot_id(golden_artifact(), 9)
val b = snapshot_id(golden_artifact(), 10)
expect(entity_ref_stale(a, a)).to_equal(false)
expect(entity_ref_stale(a, b)).to_equal(true)
expect(snapshot_supersedes(b, a)).to_equal(true)
expect(snapshot_supersedes(a, b)).to_equal(false)
```

</details>

### tagmap contract v1 — exact bytes

#### encodes a two-key TagSchema to the frozen layout

- encodes a two-key TagSchema to the frozen layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes a two-key TagSchema to the frozen layout")
val k1 = tag_key(11, 22, TagValueType.Marker, TagCardinality.One,
                 TagLifetime.Snapshot, TagMergePolicy.Replace,
                 TagAuthority.Parser)
val k2 = tag_key(33, 44, TagValueType.SourceAnchor, TagCardinality.Many,
                 TagLifetime.Artifact, TagMergePolicy.Union,
                 TagAuthority.External)
expect(wire_to_hex(encode_tag_schema(tag_schema(5, [k1, k2]))))
    .to_equal(GOLDEN_TAG_SCHEMA_TWO_KEYS)
```

</details>

#### encodes an empty TagSchema

- encodes an empty TagSchema


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes an empty TagSchema")
val none: [any] = []
expect(wire_to_hex(encode_tag_schema(tag_schema(0, none))))
    .to_equal(GOLDEN_TAG_SCHEMA_EMPTY)
```

</details>

#### keeps TagKey exactly 13 bytes

- keeps TagKey exactly 13 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("keeps TagKey exactly 13 bytes")
val k1 = tag_key(11, 22, TagValueType.Marker, TagCardinality.One,
                 TagLifetime.Snapshot, TagMergePolicy.Replace,
                 TagAuthority.Parser)
expect(encode_tag_schema(tag_schema(5, [k1])).len() - 16)
    .to_equal(TAG_KEY_LEN)
```

</details>

### tagmap contract v1 — TagValue exact bytes, all ten types

#### encodes Marker with no payload

- encodes Marker with no payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes Marker with no payload")
expect(wire_to_hex(encode_tag_value(plain_tag_value(TagValueType.Marker, 0))))
    .to_equal(GOLDEN_TV_MARKER)
```

</details>

#### encodes Bool as a single normalised byte

- encodes Bool as a single normalised byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes Bool as a single normalised byte")
expect(wire_to_hex(encode_tag_value(plain_tag_value(TagValueType.Bool, 1))))
    .to_equal(GOLDEN_TV_BOOL_TRUE)
expect(wire_to_hex(encode_tag_value(plain_tag_value(TagValueType.Bool, 0))))
    .to_equal(GOLDEN_TV_BOOL_FALSE)
```

</details>

#### normalises any non-zero Bool payload to 1

- normalises any non-zero Bool payload to 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("normalises any non-zero Bool payload to 1")
expect(wire_to_hex(encode_tag_value(plain_tag_value(TagValueType.Bool, 99))))
    .to_equal(GOLDEN_TV_BOOL_TRUE)
```

</details>

#### encodes I64

- encodes I64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes I64")
expect(wire_to_hex(encode_tag_value(
    plain_tag_value(TagValueType.I64, 0x1122334455667788))))
    .to_equal(GOLDEN_TV_I64)
```

</details>

#### encodes U64 at all-ones without sign extension

- encodes U64 at all-ones without sign extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes U64 at all-ones without sign extension")
expect(wire_to_hex(encode_tag_value(
    plain_tag_value(TagValueType.U64, 0xFFFFFFFFFFFFFFFF))))
    .to_equal(GOLDEN_TV_U64_MAX)
```

</details>

#### encodes F64 as a raw IEEE-754 bit pattern

- encodes F64 as a raw IEEE-754 bit pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes F64 as a raw IEEE-754 bit pattern")
expect(wire_to_hex(encode_tag_value(
    plain_tag_value(TagValueType.F64, 0x3FF0000000000000))))
    .to_equal(GOLDEN_TV_F64_ONE)
```

</details>

#### encodes StringId in four bytes

- encodes StringId in four bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes StringId in four bytes")
expect(wire_to_hex(encode_tag_value(
    plain_tag_value(TagValueType.StringId, 0xABCDEF01))))
    .to_equal(GOLDEN_TV_STRING_ID)
```

</details>

#### encodes an EntityRef payload

- encodes an EntityRef payload
   - Expected: wire_to_hex(encode_tag_value(v)) equals `GOLDEN_TV_ENTITY_REF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes an EntityRef payload")
val v = TagValue(value_type: TagValueType.EntityRef, num: 0,
                 ref: entity_ref(9, 8),
                 artifact: identity_zero_artifact(),
                 anchor: source_anchor_read(tagmap_zero_anchor_bytes(), 0))
expect(wire_to_hex(encode_tag_value(v))).to_equal(GOLDEN_TV_ENTITY_REF)
```

</details>

#### encodes an ArtifactId payload

- encodes an ArtifactId payload
   - Expected: wire_to_hex(encode_tag_value(v)) equals `GOLDEN_TV_ARTIFACT_ID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes an ArtifactId payload")
val v = TagValue(value_type: TagValueType.ArtifactId, num: 0,
                 ref: entity_ref(0, 0), artifact: golden_artifact(),
                 anchor: source_anchor_read(tagmap_zero_anchor_bytes(), 0))
expect(wire_to_hex(encode_tag_value(v))).to_equal(GOLDEN_TV_ARTIFACT_ID)
```

</details>

#### encodes a SourceAnchor payload

- encodes a SourceAnchor payload
   - Expected: wire_to_hex(encode_tag_value(v)) equals `GOLDEN_TV_SOURCE_ANCHOR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes a SourceAnchor payload")
val v = TagValue(value_type: TagValueType.SourceAnchor, num: 0,
                 ref: entity_ref(0, 0),
                 artifact: identity_zero_artifact(),
                 anchor: source_anchor(golden_artifact(), 100, 200, 5, 6))
expect(wire_to_hex(encode_tag_value(v))).to_equal(GOLDEN_TV_SOURCE_ANCHOR)
```

</details>

#### encodes SmallSet as a packed offset/count word

- encodes SmallSet as a packed offset/count word
   - Expected: wire_to_hex(encode_tag_value(v)) equals `GOLDEN_TV_SMALL_SET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes SmallSet as a packed offset/count word")
val v = plain_tag_value(TagValueType.SmallSet, tag_small_set_pack(77, 3))
expect(wire_to_hex(encode_tag_value(v))).to_equal(GOLDEN_TV_SMALL_SET)
```

</details>

### tagmap contract v1 — round trip and rejection

#### round-trips a multi-key schema

- round-trips a multi-key schema
   - Expected: d.ok is true
   - Expected: tag_schema_equal(d.value, s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips a multi-key schema")
val k1 = tag_key(11, 22, TagValueType.Marker, TagCardinality.One,
                 TagLifetime.Snapshot, TagMergePolicy.Replace,
                 TagAuthority.Parser)
val k2 = tag_key(33, 44, TagValueType.SourceAnchor, TagCardinality.Many,
                 TagLifetime.Artifact, TagMergePolicy.Union,
                 TagAuthority.External)
val s = tag_schema(5, [k1, k2])
val d = decode_tag_schema(encode_tag_schema(s))
expect(d.ok).to_equal(true)
expect(tag_schema_equal(d.value, s)).to_equal(true)
```

</details>

#### round-trips SmallSet offset and count through the packed word

- round-trips SmallSet offset and count through the packed word
   - Expected: d.ok is true
   - Expected: tag_small_set_offset(d.value.num) equals `77`
   - Expected: tag_small_set_count(d.value.num) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips SmallSet offset and count through the packed word")
val packed = tag_small_set_pack(77, 3)
val d = decode_tag_value(encode_tag_value(
    plain_tag_value(TagValueType.SmallSet, packed)))
expect(d.ok).to_equal(true)
expect(tag_small_set_offset(d.value.num)).to_equal(77)
expect(tag_small_set_count(d.value.num)).to_equal(3)
```

</details>

#### reports the consumed width for every value type

- reports the consumed width for every value type
   - Expected: d.ok is true
   - Expected: d.consumed equals `1 + tag_value_payload_len(TagValueType.I64)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("reports the consumed width for every value type")
val d = decode_tag_value(encode_tag_value(
    plain_tag_value(TagValueType.I64, 7)))
expect(d.ok).to_equal(true)
expect(d.consumed).to_equal(1 + tag_value_payload_len(TagValueType.I64))
```

</details>

#### rejects an unknown TagValueType discriminant rather than defaulting

- rejects an unknown TagValueType discriminant rather than defaulting
   - Expected: decode_tag_value(b).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects an unknown TagValueType discriminant rather than defaulting")
var b = encode_tag_value(plain_tag_value(TagValueType.Marker, 0))
b[8] = 200
expect(decode_tag_value(b).ok).to_equal(false)
```

</details>

#### rejects an unknown enum discriminant inside a TagKey

- rejects an unknown enum discriminant inside a TagKey
   - Expected: decode_tag_schema(b).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects an unknown enum discriminant inside a TagKey")
val k1 = tag_key(11, 22, TagValueType.Marker, TagCardinality.One,
                 TagLifetime.Snapshot, TagMergePolicy.Replace,
                 TagAuthority.Parser)
var b = encode_tag_schema(tag_schema(5, [k1]))
# byte 16 is the first TagKey's value_type slot
b[24] = 250
expect(decode_tag_schema(b).ok).to_equal(false)
```

</details>

#### rejects a schema whose declared key count exceeds the buffer

- rejects a schema whose declared key count exceeds the buffer
   - Expected: decode_tag_schema(b).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a schema whose declared key count exceeds the buffer")
val k1 = tag_key(11, 22, TagValueType.Marker, TagCardinality.One,
                 TagLifetime.Snapshot, TagMergePolicy.Replace,
                 TagAuthority.Parser)
var b = encode_tag_schema(tag_schema(5, [k1]))
b[12] = 9
expect(decode_tag_schema(b).ok).to_equal(false)
```

</details>

#### bounds every enum validator at its frozen maximum

- bounds every enum validator at its frozen maximum
   - Expected: tag_value_type_valid(9) is true
   - Expected: tag_value_type_valid(10) is false
   - Expected: tag_value_type_valid(0 - 1) is false
   - Expected: tag_cardinality_valid(2) is true
   - Expected: tag_cardinality_valid(3) is false
   - Expected: tag_authority_valid(5) is true
   - Expected: tag_authority_valid(6) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("bounds every enum validator at its frozen maximum")
expect(tag_value_type_valid(9)).to_equal(true)
expect(tag_value_type_valid(10)).to_equal(false)
expect(tag_value_type_valid(0 - 1)).to_equal(false)
expect(tag_cardinality_valid(2)).to_equal(true)
expect(tag_cardinality_valid(3)).to_equal(false)
expect(tag_authority_valid(5)).to_equal(true)
expect(tag_authority_valid(6)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/identity_tagmap_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering identity contract v1 — exact bytes, identity contract v1 — round trip, identity contract v1 — rejection rules (arch 30.1), tagmap contract v1 — exact bytes, tagmap contract v1 — TagValue exact bytes, all ten types, tagmap contract v1 — round trip and rejection.
- identity contract v1 — exact bytes
- identity contract v1 — round trip
- identity contract v1 — rejection rules (arch 30.1)
- tagmap contract v1 — exact bytes
- tagmap contract v1 — TagValue exact bytes, all ten types
- tagmap contract v1 — round trip and rejection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMMON`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db8df27944217b3869a4035fd5cff31a70a4f4e2fba4c2f5ab99b3d3c50d3ea5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db8df27944217b3869a4035fd5cff31a70a4f4e2fba4c2f5ab99b3d3c50d3ea5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db8df27944217b3869a4035fd5cff31a70a4f4e2fba4c2f5ab99b3d3c50d3ea5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/common/structural/identity_tagmap_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/identity_tagmap_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/identity_tagmap_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/identity_tagmap_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/identity_tagmap_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/common/structural/identity_tagmap_contract_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes EntityRef to the frozen 8-byte body, zero case' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/identity_tagmap_contract_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes EntityRef all-ones without sign extension' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/identity_tagmap_contract_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes EntityRef little-endian in field order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
