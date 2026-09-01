# Mapping Contract Specification

> Tests covering MappingKind wire discriminants, OriginPolicy wire discriminants, MappingEdge — exact bytes, MappingEdge — round trip and rejection, MappingKindSet, MappingShard — exact bytes, MappingShard — round trip, MappingShard — CSR invariants, MappingShard — rejection, MappingReadPort reference semantics, MappingFlags vocabulary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 52 | 52 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mapping Contract Specification

## Scenarios

### MappingKind wire discriminants

#### assigns the 17 architecture variants to 0..16 in declaration order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- assigns the 17 architecture variants to 0..16 in declaration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the 17 architecture variants to 0..16 in declaration order")
assert_equal(mapping_kind_to_u8(MappingKind.ParsedFrom), 0)
assert_equal(mapping_kind_to_u8(MappingKind.LoweredFrom), 4)
assert_equal(mapping_kind_to_u8(MappingKind.LinkedFrom), 10)
assert_equal(mapping_kind_to_u8(MappingKind.Styles), 11)
assert_equal(mapping_kind_to_u8(MappingKind.InvalidatedBy), 16)
```

</details>

#### declares exactly 17 kinds with 16 as the maximum discriminant

- declares exactly 17 kinds with 16 as the maximum discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares exactly 17 kinds with 16 as the maximum discriminant")
assert_equal(MAPPING_KIND_COUNT, 17)
assert_equal(MAPPING_KIND_MAX, 16)
```

</details>

#### round-trips every discriminant through from_u8

- round-trips every discriminant through from_u8


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every discriminant through from_u8")
var i = 0
var mismatches = 0
while i <= MAPPING_KIND_MAX:
    if mapping_kind_to_u8(mapping_kind_from_u8(i)) != i:
        mismatches = mismatches + 1
    i = i + 1
assert_equal(mismatches, 0)
```

</details>

#### rejects a discriminant past the end of the frozen enum

- rejects a discriminant past the end of the frozen enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a discriminant past the end of the frozen enum")
assert_true(mapping_kind_valid(16))
assert_false(mapping_kind_valid(17))
assert_false(mapping_kind_valid(-1))
assert_false(mapping_kind_valid(255))
```

</details>

### OriginPolicy wire discriminants

#### assigns the six architecture variants to 0..5 in declaration order

- assigns the six architecture variants to 0..5 in declaration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the six architecture variants to 0..5 in declaration order")
assert_equal(origin_policy_to_u8(OriginPolicy.PreserveOneToOne), 0)
assert_equal(origin_policy_to_u8(OriginPolicy.Split), 1)
assert_equal(origin_policy_to_u8(OriginPolicy.Merge), 2)
assert_equal(origin_policy_to_u8(OriginPolicy.Clone), 3)
assert_equal(origin_policy_to_u8(OriginPolicy.Synthesize), 4)
assert_equal(origin_policy_to_u8(OriginPolicy.DiscardWithReason), 5)
```

</details>

#### rejects an unknown policy discriminant

- rejects an unknown policy discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown policy discriminant")
assert_true(origin_policy_valid(5))
assert_false(origin_policy_valid(6))
assert_equal(origin_policy_to_u8(origin_policy_from_u8(3)), 3)
```

</details>

### MappingEdge — exact bytes

#### encodes the zero edge to the frozen 27-byte body

- encodes the zero edge to the frozen 27-byte body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the zero edge to the frozen 27-byte body")
expect(wire_to_hex(encode_mapping_edge(
    mapping_edge(entity_ref(0, 0), entity_ref(0, 0),
                 MappingKind.ParsedFrom, 0, 0, 0))))
    .to_equal(GOLDEN_EDGE_ZERO)
```

</details>

#### encodes every field asymmetrically so field order is pinned

- encodes every field asymmetrically so field order is pinned


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes every field asymmetrically so field order is pinned")
expect(wire_to_hex(encode_mapping_edge(
    mapping_edge(entity_ref(1, 2), entity_ref(3, 4),
                 MappingKind.LoweredFrom, 0x11223344,
                 MAPPING_FLAG_WEIGHT_VALID, 600))))
    .to_equal(GOLDEN_EDGE_BASIC)
```

</details>

#### encodes the all-ones edge without sign extension

- encodes the all-ones edge without sign extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the all-ones edge without sign extension")
expect(wire_to_hex(encode_mapping_edge(
    mapping_edge(entity_ref(0xFFFFFFFF, 0xFFFFFFFF),
                 entity_ref(0xFFFFFFFF, 0xFFFFFFFF),
                 MappingKind.InvalidatedBy, 0xFFFFFFFF, 7, 0xFFFF))))
    .to_equal(GOLDEN_EDGE_MAX)
```

</details>

#### encodes a synthesized, discarded origin

- encodes a synthesized, discarded origin


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a synthesized, discarded origin")
expect(wire_to_hex(encode_mapping_edge(
    mapping_edge(entity_ref(0, 0), entity_ref(7, 9),
                 MappingKind.GeneratedFrom, 2,
                 MAPPING_FLAG_SYNTHETIC + MAPPING_FLAG_DISCARDED, 0))))
    .to_equal(GOLDEN_EDGE_SYNTHETIC)
```

</details>

#### occupies exactly 27 bytes of body

- occupies exactly 27 bytes of body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("occupies exactly 27 bytes of body")
assert_equal(MAPPING_EDGE_LEN, 27)
assert_equal(encode_mapping_edge(
    mapping_edge(entity_ref(1, 2), entity_ref(3, 4),
                 MappingKind.LoweredFrom, 1, 1, 600)).len(), 35)
```

</details>

### MappingEdge — round trip and rejection

#### reconstructs an edge through decode(encode(x))

- reconstructs an edge through decode(encode(x))


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs an edge through decode(encode(x))")
val e = mapping_edge(entity_ref(1, 2), entity_ref(3, 4),
                     MappingKind.LoweredFrom, 0x11223344,
                     MAPPING_FLAG_WEIGHT_VALID, 600)
val r = decode_mapping_edge(encode_mapping_edge(e))
assert_true(r.ok)
assert_true(mapping_edge_equal(r.value, e))
```

</details>

#### rejects an unknown kind discriminant instead of defaulting

- rejects an unknown kind discriminant instead of defaulting


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown kind discriminant instead of defaulting")
val e = mapping_edge(entity_ref(1, 2), entity_ref(3, 4),
                     MappingKind.LoweredFrom, 1, 0, 0)
val bad = corrupt_byte(encode_mapping_edge(e), 24, 17)
assert_false(decode_mapping_edge(bad).ok)
```

</details>

#### rejects a set reserved flag bit

- rejects a set reserved flag bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a set reserved flag bit")
val e = mapping_edge(entity_ref(1, 2), entity_ref(3, 4),
                     MappingKind.LoweredFrom, 1, 0, 0)
val bad = corrupt_byte(encode_mapping_edge(e), 29, 8)
assert_false(decode_mapping_edge(bad).ok)
```

</details>

#### rejects a truncated edge

- rejects a truncated edge


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a truncated edge")
val e = mapping_edge(entity_ref(1, 2), entity_ref(3, 4),
                     MappingKind.LoweredFrom, 1, 0, 0)
assert_false(decode_mapping_edge(truncated(encode_mapping_edge(e), 30)).ok)
```

</details>

#### rejects a shard buffer offered to the edge decoder

- rejects a shard buffer offered to the edge decoder


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a shard buffer offered to the edge decoder")
assert_false(decode_mapping_edge(encode_mapping_shard(fixture_forward_shard())).ok)
```

</details>

#### treats a missing WEIGHT_VALID bit as a full share, not as zero

- treats a missing WEIGHT_VALID bit as a full share, not as zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a missing WEIGHT_VALID bit as a full share, not as zero")
val no_w = mapping_edge(entity_ref(0, 0), entity_ref(0, 1),
                        MappingKind.LoweredFrom, 1, MAPPING_FLAG_NONE, 0)
val with_w = mapping_edge(entity_ref(0, 0), entity_ref(0, 1),
                          MappingKind.OptimizedFrom, 1,
                          MAPPING_FLAG_WEIGHT_VALID, 400)
assert_equal(mapping_edge_weight_or_default(no_w), 1000)
assert_equal(mapping_edge_weight_or_default(with_w), 400)
```

</details>

### MappingKindSet

#### encodes the empty mask to the frozen bytes

- encodes the empty mask to the frozen bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the empty mask to the frozen bytes")
expect(wire_to_hex(encode_mapping_kind_set(MAPPING_KIND_SET_EMPTY)))
    .to_equal(GOLDEN_KIND_SET_EMPTY)
```

</details>

#### encodes the all-kinds mask as 17 set bits

- encodes the all-kinds mask as 17 set bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the all-kinds mask as 17 set bits")
assert_equal(MAPPING_KIND_SET_ALL, 131071)
expect(wire_to_hex(encode_mapping_kind_set(MAPPING_KIND_SET_ALL)))
    .to_equal(GOLDEN_KIND_SET_ALL)
```

</details>

#### encodes {LayoutOf, PaintOf} to the frozen bit positions

- encodes {LayoutOf, PaintOf} to the frozen bit positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes {LayoutOf, PaintOf} to the frozen bit positions")
var kinds: [MappingKind] = []
kinds.push(MappingKind.LayoutOf)
kinds.push(MappingKind.PaintOf)
expect(wire_to_hex(encode_mapping_kind_set(mapping_kind_set_of(kinds))))
    .to_equal(GOLDEN_KIND_SET_LAYOUT_PAINT)
```

</details>

#### answers membership by discriminant bit

- answers membership by discriminant bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("answers membership by discriminant bit")
val s = mapping_kind_set_add(MAPPING_KIND_SET_EMPTY, MappingKind.InvalidatedBy)
assert_true(mapping_kind_set_contains(s, MappingKind.InvalidatedBy))
assert_false(mapping_kind_set_contains(s, MappingKind.ParsedFrom))
```

</details>

#### rejects a mask with a reserved bit set

- rejects a mask with a reserved bit set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a mask with a reserved bit set")
assert_true(mapping_kind_set_valid(MAPPING_KIND_SET_ALL))
assert_false(mapping_kind_set_valid(131072))
assert_false(decode_mapping_kind_set(
    corrupt_byte(encode_mapping_kind_set(MAPPING_KIND_SET_ALL), 10, 0x03)).ok)
```

</details>

#### round-trips a mask

- round-trips a mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a mask")
val r = decode_mapping_kind_set(encode_mapping_kind_set(24576))
assert_true(r.ok)
assert_equal(r.value, 24576)
```

</details>

### MappingShard — exact bytes

#### encodes the empty shard with its CSR terminator

- encodes the empty shard with its CSR terminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the empty shard with its CSR terminator")
val off: [u32] = [0]
val none: [MappingEdge] = []
expect(wire_to_hex(encode_mapping_shard(mapping_shard_forward(1, 0, off, none))))
    .to_equal(GOLDEN_SHARD_EMPTY)
```

</details>

#### encodes the forward-only shard to the frozen bytes

- encodes the forward-only shard to the frozen bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the forward-only shard to the frozen bytes")
expect(wire_to_hex(encode_mapping_shard(fixture_forward_shard())))
    .to_equal(GOLDEN_SHARD_FORWARD)
```

</details>

#### encodes the shard with a lazily built reverse index

- encodes the shard with a lazily built reverse index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the shard with a lazily built reverse index")
expect(wire_to_hex(encode_mapping_shard(
    mapping_build_reverse(fixture_forward_shard(), 3))))
    .to_equal(GOLDEN_SHARD_REVERSE)
```

</details>

### MappingShard — round trip

#### reconstructs a forward-only shard

- reconstructs a forward-only shard


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs a forward-only shard")
val s = fixture_forward_shard()
val r = decode_mapping_shard(encode_mapping_shard(s))
assert_true(r.ok)
assert_true(mapping_shard_equal(r.value, s))
```

</details>

#### reconstructs a shard carrying a reverse index

- reconstructs a shard carrying a reverse index


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs a shard carrying a reverse index")
val s = mapping_build_reverse(fixture_forward_shard(), 3)
val r = decode_mapping_shard(encode_mapping_shard(s))
assert_true(r.ok)
assert_true(mapping_shard_equal(r.value, s))
```

</details>

#### builds the reverse index deterministically by target index

- builds the reverse index deterministically by target index


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds the reverse index deterministically by target index")
val s = mapping_build_reverse(fixture_forward_shard(), 3)
assert_equal(s.reverse_offsets.len(), 4)
assert_equal(s.reverse_offsets[0], 0)
assert_equal(s.reverse_offsets[1], 0)
assert_equal(s.reverse_offsets[2], 1)
assert_equal(s.reverse_offsets[3], 3)
assert_equal(s.reverse_edges.len(), 3)
```

</details>

### MappingShard — CSR invariants

#### accepts a well-formed offset array

- accepts a well-formed offset array


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a well-formed offset array")
assert_true(mapping_offsets_well_formed(fixture_offsets(), 2, 3))
```

</details>

#### rejects an offset array of the wrong length

- rejects an offset array of the wrong length


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an offset array of the wrong length")
assert_false(mapping_offsets_well_formed(fixture_offsets(), 3, 3))
```

</details>

#### rejects an offset array that does not start at zero

- rejects an offset array that does not start at zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an offset array that does not start at zero")
var o: [u32] = []
o.push(1)
o.push(2)
o.push(3)
assert_false(mapping_offsets_well_formed(o, 2, 3))
```

</details>

#### rejects an offset array that does not end at the edge count

- rejects an offset array that does not end at the edge count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an offset array that does not end at the edge count")
var o: [u32] = []
o.push(0)
o.push(2)
o.push(9)
assert_false(mapping_offsets_well_formed(o, 2, 3))
```

</details>

#### rejects a decreasing offset array

- rejects a decreasing offset array


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a decreasing offset array")
var o: [u32] = []
o.push(0)
o.push(3)
o.push(3)
assert_true(mapping_offsets_well_formed(o, 2, 3))
var d: [u32] = []
d.push(0)
d.push(5)
d.push(3)
assert_false(mapping_offsets_well_formed(d, 2, 3))
```

</details>

#### considers the fixture shards structurally valid

- considers the fixture shards structurally valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("considers the fixture shards structurally valid")
assert_true(mapping_shard_valid(fixture_forward_shard()))
assert_true(mapping_shard_valid(mapping_build_reverse(fixture_forward_shard(), 3)))
```

</details>

#### rejects a shard whose reverse index points past the edge list

- rejects a shard whose reverse index points past the edge list


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a shard whose reverse index points past the edge list")
var ro: [u32] = []
ro.push(0)
ro.push(1)
var re: [u32] = []
re.push(99)
assert_false(mapping_shard_valid(
    mapping_shard(1, 2, fixture_offsets(), fixture_edges(), 1, ro, re)))
```

</details>

#### refuses to encode a structurally invalid shard at all

- refuses to encode a structurally invalid shard at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to encode a structurally invalid shard at all")
var bad: [u32] = []
bad.push(0)
bad.push(9)
bad.push(3)
assert_equal(encode_mapping_shard(
    mapping_shard_forward(1, 2, bad, fixture_edges())).len(), 0)
```

</details>

### MappingShard — rejection

#### rejects a corrupted from_offsets terminator

- rejects a corrupted from_offsets terminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a corrupted from_offsets terminator")
# Byte 29 is the low byte of from_offsets[2], the CSR terminator:
# envelope 0..7 | version 8..11 | node_count 12..15 | edge_count 16..19
# | has_reverse 20 | from_offsets 21..32. Setting it to 9 makes the
# array claim 9 edges while the header declares 3.
val bytes = encode_mapping_shard(fixture_forward_shard())
assert_false(decode_mapping_shard(corrupt_byte(bytes, 29, 9)).ok)
```

</details>

#### rejects a has_reverse byte outside {0, 1}

- rejects a has_reverse byte outside {0, 1}


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a has_reverse byte outside {0, 1}")
val bytes = encode_mapping_shard(fixture_forward_shard())
assert_false(decode_mapping_shard(corrupt_byte(bytes, 20, 2)).ok)
```

</details>

#### rejects a truncated shard

- rejects a truncated shard


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a truncated shard")
val bytes = encode_mapping_shard(fixture_forward_shard())
assert_false(decode_mapping_shard(truncated(bytes, bytes.len() - 1)).ok)
```

</details>

#### rejects trailing bytes after a complete shard

- rejects trailing bytes after a complete shard


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects trailing bytes after a complete shard")
var bytes = encode_mapping_shard(fixture_forward_shard())
bytes.push(0)
assert_false(decode_mapping_shard(bytes).ok)
```

</details>

#### rejects an edge-typed buffer offered to the shard decoder

- rejects an edge-typed buffer offered to the shard decoder


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an edge-typed buffer offered to the shard decoder")
assert_false(decode_mapping_shard(encode_mapping_edge(
    mapping_edge(entity_ref(1, 2), entity_ref(3, 4),
                 MappingKind.LoweredFrom, 1, 0, 0))).ok)
```

</details>

#### rejects a wrong schema version

- rejects a wrong schema version


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a wrong schema version")
val bytes = encode_mapping_shard(fixture_forward_shard())
assert_equal(MAPPING_SCHEMA_VERSION, 1)
assert_false(decode_mapping_shard(corrupt_byte(bytes, 4, 2)).ok)
```

</details>

#### rejects a non-zero envelope reserved field

- rejects a non-zero envelope reserved field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a non-zero envelope reserved field")
val bytes = encode_mapping_shard(fixture_forward_shard())
assert_false(decode_mapping_shard(corrupt_byte(bytes, 6, 1)).ok)
```

</details>

### MappingReadPort reference semantics

#### returns only the edges leaving the queried node

- returns only the edges leaving the queried node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns only the edges leaving the queried node")
val s = fixture_forward_shard()
assert_equal(mapping_forward_edges(s, 0, MAPPING_KIND_SET_ALL).len(), 2)
assert_equal(mapping_forward_edges(s, 1, MAPPING_KIND_SET_ALL).len(), 1)
```

</details>

#### filters forward edges by kind mask

- filters forward edges by kind mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters forward edges by kind mask")
val s = fixture_forward_shard()
val only_lowered = mapping_kind_set_add(MAPPING_KIND_SET_EMPTY,
                                        MappingKind.LoweredFrom)
assert_equal(mapping_forward_edges(s, 0, only_lowered).len(), 2)
assert_equal(mapping_forward_edges(s, 1, only_lowered).len(), 0)
```

</details>

#### misses rather than traps on a node outside the shard

- misses rather than traps on a node outside the shard


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("misses rather than traps on a node outside the shard")
val s = fixture_forward_shard()
assert_equal(mapping_forward_edges(s, 99, MAPPING_KIND_SET_ALL).len(), 0)
assert_equal(mapping_forward_edges(s, -1, MAPPING_KIND_SET_ALL).len(), 0)
```

</details>

#### returns nothing in reverse until the reverse index is demanded

- returns nothing in reverse until the reverse index is demanded


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nothing in reverse until the reverse index is demanded")
assert_equal(mapping_reverse_edges(fixture_forward_shard(), 2,
                                   MAPPING_KIND_SET_ALL).len(), 0)
```

</details>

#### traces many-to-one provenance once the reverse index exists

- traces many-to-one provenance once the reverse index exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traces many-to-one provenance once the reverse index exists")
val s = mapping_build_reverse(fixture_forward_shard(), 3)
assert_equal(mapping_reverse_edges(s, 0, MAPPING_KIND_SET_ALL).len(), 0)
assert_equal(mapping_reverse_edges(s, 1, MAPPING_KIND_SET_ALL).len(), 1)
assert_equal(mapping_reverse_edges(s, 2, MAPPING_KIND_SET_ALL).len(), 2)
```

</details>

#### filters reverse edges by kind mask

- filters reverse edges by kind mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters reverse edges by kind mask")
val s = mapping_build_reverse(fixture_forward_shard(), 3)
val only_opt = mapping_kind_set_add(MAPPING_KIND_SET_EMPTY,
                                    MappingKind.OptimizedFrom)
assert_equal(mapping_reverse_edges(s, 2, only_opt).len(), 1)
```

</details>

### MappingFlags vocabulary

#### accepts only the three derived bits

- accepts only the three derived bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts only the three derived bits")
assert_true(mapping_flags_valid(0))
assert_true(mapping_flags_valid(7))
assert_false(mapping_flags_valid(8))
assert_false(mapping_flags_valid(-1))
```

</details>

#### assigns the derived bits to distinct powers of two

- assigns the derived bits to distinct powers of two


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the derived bits to distinct powers of two")
assert_equal(MAPPING_FLAG_WEIGHT_VALID, 1)
assert_equal(MAPPING_FLAG_SYNTHETIC, 2)
assert_equal(MAPPING_FLAG_DISCARDED, 4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/mapping_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MappingKind wire discriminants, OriginPolicy wire discriminants, MappingEdge — exact bytes, MappingEdge — round trip and rejection, MappingKindSet, MappingShard — exact bytes, MappingShard — round trip, MappingShard — CSR invariants, MappingShard — rejection, MappingReadPort reference semantics, MappingFlags vocabulary.
- MappingKind wire discriminants
- OriginPolicy wire discriminants
- MappingEdge — exact bytes
- MappingEdge — round trip and rejection
- MappingKindSet
- MappingShard — exact bytes
- MappingShard — round trip
- MappingShard — CSR invariants
- MappingShard — rejection
- MappingReadPort reference semantics
- MappingFlags vocabulary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 52 |
| Active scenarios | 52 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aa9d982a563c7edc7bfe339825596a003d810430fadf6876c3122a43a9834ed5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aa9d982a563c7edc7bfe339825596a003d810430fadf6876c3122a43a9834ed5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aa9d982a563c7edc7bfe339825596a003d810430fadf6876c3122a43a9834ed5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/structural/mapping_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/mapping_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/mapping_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/mapping_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/mapping_contract_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns the 17 architecture variants to 0..16 in declaration order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/mapping_contract_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares exactly 17 kinds with 16 as the maximum discriminant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/mapping_contract_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every discriminant through from_u8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
