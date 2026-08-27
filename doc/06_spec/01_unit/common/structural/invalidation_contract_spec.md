# Invalidation Contract Specification

> Tests covering DirtyMask wire bit positions, Layout-lane DIRTY_* reconciliation onto the canonical bits, DirtyMask exact bytes, DirtyMask round trip and rejection, InvalidationEdgeKind wire discriminants, InvalidationEdge exact bytes, InvalidationEdge round trip and rejection, InvalidationEdgeBatch exact bytes, InvalidationEdgeBatch structure and traversal, InvalidationEdgeBatch round trip and rejection, One-hop propagation composes DirtyMask with InvalidationEdge, Schema version.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 57 | 57 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Invalidation Contract Specification

## Scenarios

### DirtyMask wire bit positions

#### assigns the 21 architecture stages to bits 0..20 in declaration order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- assigns the 21 architecture stages to bits 0..20 in declaration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the 21 architecture stages to bits 0..20 in declaration order")
assert_equal(DIRTY_BIT_SOURCE, 1)
assert_equal(DIRTY_BIT_TOKEN, 2)
assert_equal(DIRTY_BIT_PARSE, 4)
assert_equal(DIRTY_BIT_SYNTAX_INDEX, 8)
assert_equal(DIRTY_BIT_SEMANTIC, 16)
assert_equal(DIRTY_BIT_HIR, 32)
assert_equal(DIRTY_BIT_MIR, 64)
assert_equal(DIRTY_BIT_OPTIMIZATION, 128)
assert_equal(DIRTY_BIT_CODEGEN, 256)
assert_equal(DIRTY_BIT_LINK, 512)
assert_equal(DIRTY_BIT_DOM_STRUCTURE, 1024)
assert_equal(DIRTY_BIT_SELECTOR_INDEX, 2048)
assert_equal(DIRTY_BIT_CASCADE, 4096)
assert_equal(DIRTY_BIT_COMPUTED_STYLE, 8192)
assert_equal(DIRTY_BIT_INTRINSIC_MEASURE, 16384)
assert_equal(DIRTY_BIT_LAYOUT, 32768)
assert_equal(DIRTY_BIT_PAINT, 65536)
assert_equal(DIRTY_BIT_COMPOSITE, 131072)
assert_equal(DIRTY_BIT_HIT_TEST, 262144)
assert_equal(DIRTY_BIT_ACCESSIBILITY, 524288)
assert_equal(DIRTY_BIT_RESOURCE, 1048576)
```

</details>

#### pins the vocabulary size, width and the all-known mask

- pins the vocabulary size, width and the all-known mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the vocabulary size, width and the all-known mask")
assert_equal(DIRTY_MASK_COUNT, 21)
assert_equal(DIRTY_MASK_MAX_BIT_INDEX, 20)
assert_equal(DIRTY_MASK_LEN, 4)
assert_equal(DIRTY_MASK_KNOWN, 2097151)
assert_equal(DIRTY_MASK_EMPTY, 0)
```

</details>

#### derives each bit from its index and refuses an out-of-range index

- derives each bit from its index and refuses an out-of-range index


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives each bit from its index and refuses an out-of-range index")
assert_equal(dirty_bit_of_index(0), DIRTY_BIT_SOURCE)
assert_equal(dirty_bit_of_index(14), DIRTY_BIT_INTRINSIC_MEASURE)
assert_equal(dirty_bit_of_index(20), DIRTY_BIT_RESOURCE)
assert_equal(dirty_bit_of_index(21), 0)
assert_equal(dirty_bit_of_index(-1), 0)
assert_equal(dirty_bit_of_index(64), 0)
```

</details>

#### accepts every known mask and hard-rejects a reserved bit

- accepts every known mask and hard-rejects a reserved bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts every known mask and hard-rejects a reserved bit")
assert_true(dirty_mask_valid(DIRTY_MASK_EMPTY))
assert_true(dirty_mask_valid(DIRTY_MASK_KNOWN))
assert_true(dirty_mask_valid(DIRTY_BIT_RESOURCE))
# bit 21 is the first reserved position.
assert_false(dirty_mask_valid(2097152))
assert_false(dirty_mask_valid(DIRTY_MASK_KNOWN + 1))
# A u64 pattern with the top bit set arrives as a negative i64.
assert_false(dirty_mask_valid(-1))
```

</details>

#### composes masks by union, intersection and membership

- composes masks by union, intersection and membership


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("composes masks by union, intersection and membership")
val m = dirty_mask_of_bits([DIRTY_BIT_LAYOUT, DIRTY_BIT_HIT_TEST])
assert_equal(m, 294912)
assert_true(dirty_mask_contains(m, DIRTY_BIT_LAYOUT))
assert_false(dirty_mask_contains(m, DIRTY_BIT_PAINT))
# An empty probe is not "contained": a caller asking whether nothing is
# dirty must use dirty_mask_is_empty, not a zero membership probe.
assert_false(dirty_mask_contains(m, 0))
assert_equal(dirty_mask_union(DIRTY_BIT_LAYOUT, DIRTY_BIT_HIT_TEST), m)
assert_equal(dirty_mask_intersect(m, DIRTY_BIT_LAYOUT), DIRTY_BIT_LAYOUT)
assert_true(dirty_mask_is_empty(DIRTY_MASK_EMPTY))
assert_false(dirty_mask_is_empty(m))
```

</details>

### Layout-lane DIRTY_* reconciliation onto the canonical bits

#### puts the four layout constants on their canonical §9.1 bits

- puts the four layout constants on their canonical §9.1 bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("puts the four layout constants on their canonical §9.1 bits")
# contracts.spl originally packed the four stages the layout lane cared
# about into bits 0..3, so bit 0 meant IntrinsicMeasure to the layout
# lane and Source on the wire. Now reconciled onto the §9.1 positions.
# The renumber was legal precisely because nothing had serialized a
# layout-built mask yet: no golden vector was ever authored in the
# layout vocabulary, and every consumer composes these symbolically.
assert_equal(DIRTY_NONE, 0)
assert_equal(DIRTY_INTRINSIC_MEASURE, 16384)
assert_equal(DIRTY_LAYOUT, 32768)
assert_equal(DIRTY_HIT_TEST, 262144)
assert_equal(DIRTY_RESOURCE, 1048576)
```

</details>

#### makes the layout constants identical to the canonical vocabulary

- makes the layout constants identical to the canonical vocabulary


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes the layout constants identical to the canonical vocabulary")
assert_equal(DIRTY_INTRINSIC_MEASURE, DIRTY_BIT_INTRINSIC_MEASURE)
assert_equal(DIRTY_LAYOUT, DIRTY_BIT_LAYOUT)
assert_equal(DIRTY_HIT_TEST, DIRTY_BIT_HIT_TEST)
assert_equal(DIRTY_RESOURCE, DIRTY_BIT_RESOURCE)
# The empty mask is the one value both numberings always agreed on.
assert_equal(DIRTY_NONE, DIRTY_MASK_EMPTY)
```

</details>

#### accepts every layout constant as a valid wire mask

- accepts every layout constant as a valid wire mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts every layout constant as a valid wire mask")
# Under the old 1/2/4/8 packing these passed this check too, but as the
# WRONG stages. Validity alone was never the property that mattered.
assert_true(dirty_mask_valid(DIRTY_INTRINSIC_MEASURE))
assert_true(dirty_mask_valid(DIRTY_LAYOUT))
assert_true(dirty_mask_valid(DIRTY_HIT_TEST))
assert_true(dirty_mask_valid(DIRTY_RESOURCE))
assert_true(dirty_mask_valid(
    DIRTY_INTRINSIC_MEASURE | DIRTY_LAYOUT | DIRTY_HIT_TEST
    | DIRTY_RESOURCE))
```

</details>

#### encodes a layout-composed mask to the canonical golden bytes

- encodes a layout-composed mask to the canonical golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a layout-composed mask to the canonical golden bytes")
# This is the property the renumber exists to buy, and the assertion
# that would have caught the divergence had it existed earlier: a mask
# composed from the LAYOUT vocabulary now serializes to exactly the
# bytes the canonical vocabulary produces for the same stages.
# Under the old packing DIRTY_LAYOUT | DIRTY_HIT_TEST was 6 and encoded
# to "06000000" — {Token, Parse} on the wire, two stages that have
# nothing to do with layout.
assert_equal(
    wire_to_hex(encode_dirty_mask(mask(DIRTY_LAYOUT | DIRTY_HIT_TEST))),
    GOLDEN_DIRTY_LAYOUT_HITTEST)
assert_equal(
    wire_to_hex(encode_dirty_mask(
        mask(DIRTY_INTRINSIC_MEASURE | DIRTY_LAYOUT | DIRTY_HIT_TEST))),
    GOLDEN_DIRTY_INTRINSIC_CHAIN)
```

</details>

### DirtyMask exact bytes

#### encodes the empty mask to the golden vector

- encodes the empty mask to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the empty mask to the golden vector")
assert_equal(wire_to_hex(encode_dirty_mask(mask(0))), GOLDEN_DIRTY_NONE)
```

</details>

#### encodes {Source} to the golden vector that pins bit 0

- encodes {Source} to the golden vector that pins bit 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes {Source} to the golden vector that pins bit 0")
assert_equal(wire_to_hex(encode_dirty_mask(mask(DIRTY_BIT_SOURCE))),
             GOLDEN_DIRTY_SOURCE)
```

</details>

#### encodes {Layout, HitTest} to the golden vector

- encodes {Layout, HitTest} to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes {Layout, HitTest} to the golden vector")
assert_equal(
    wire_to_hex(encode_dirty_mask(
        mask(DIRTY_BIT_LAYOUT | DIRTY_BIT_HIT_TEST))),
    GOLDEN_DIRTY_LAYOUT_HITTEST)
```

</details>

#### encodes the font-metric consequence set to the golden vector

- encodes the font-metric consequence set to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the font-metric consequence set to the golden vector")
assert_equal(
    wire_to_hex(encode_dirty_mask(
        mask(DIRTY_BIT_INTRINSIC_MEASURE | DIRTY_BIT_LAYOUT
             | DIRTY_BIT_HIT_TEST))),
    GOLDEN_DIRTY_INTRINSIC_CHAIN)
```

</details>

#### encodes the all-known mask to the golden vector

- encodes the all-known mask to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the all-known mask to the golden vector")
assert_equal(wire_to_hex(encode_dirty_mask(mask(DIRTY_MASK_KNOWN))),
             GOLDEN_DIRTY_ALL)
```

</details>

#### emits exactly envelope + 4 bytes

- emits exactly envelope + 4 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exactly envelope + 4 bytes")
assert_equal(encode_dirty_mask(mask(DIRTY_MASK_KNOWN)).len(),
             WIRE_ENVELOPE_LEN + DIRTY_MASK_LEN)
```

</details>

### DirtyMask round trip and rejection

#### round-trips every golden mask

- round-trips every golden mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every golden mask")
val cases = [0, DIRTY_BIT_SOURCE, DIRTY_BIT_LAYOUT | DIRTY_BIT_HIT_TEST,
             DIRTY_MASK_KNOWN]
var i = 0
while i < cases.len():
    val r = decode_dirty_mask(encode_dirty_mask(mask(cases[i])))
    assert_true(r.ok)
    assert_true(dirty_mask_equal(r.value, mask(cases[i])))
    assert_equal(dirty_mask_raw(r.value), cases[i])
    i = i + 1
```

</details>

#### refuses to ENCODE a mask with a reserved bit

- refuses to ENCODE a mask with a reserved bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to ENCODE a mask with a reserved bit")
# The invariant is enforced on encode as well as decode: a producer must
# not be able to put a reserved bit on the wire and blame the reader.
assert_equal(encode_dirty_mask(mask(2097152)).len(), 0)
assert_equal(encode_dirty_mask(mask(-1)).len(), 0)
```

</details>

#### hard-rejects a decoded reserved bit instead of masking it off

- hard-rejects a decoded reserved bit instead of masking it off


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects a decoded reserved bit instead of masking it off")
val good = encode_dirty_mask(mask(DIRTY_MASK_KNOWN))
# byte 10 carries mask bits 16..23; 0xff sets reserved bits 21, 22, 23.
val bad = corrupt_byte(good, 10, 255)
assert_false(decode_dirty_mask(bad).ok)
```

</details>

#### rejects a wrong magic, a wrong version and a bad reserved word

- rejects a wrong magic, a wrong version and a bad reserved word


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a wrong magic, a wrong version and a bad reserved word")
val good = encode_dirty_mask(mask(DIRTY_BIT_SOURCE))
assert_false(decode_dirty_mask(corrupt_byte(good, 0, 88)).ok)
assert_false(decode_dirty_mask(corrupt_byte(good, 4, 2)).ok)
assert_false(decode_dirty_mask(corrupt_byte(good, 6, 1)).ok)
```

</details>

#### rejects truncation and trailing bytes

- rejects truncation and trailing bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncation and trailing bytes")
val good = encode_dirty_mask(mask(DIRTY_BIT_SOURCE))
assert_false(decode_dirty_mask(truncated(good, good.len() - 1)).ok)
var longer = good
longer.push(0)
assert_false(decode_dirty_mask(longer).ok)
```

</details>

#### rejects an InvalidationEdge buffer offered as a DirtyMask

- rejects an InvalidationEdge buffer offered as a DirtyMask


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an InvalidationEdge buffer offered as a DirtyMask")
val e = invalidation_edge(entity_ref(1, 2), entity_ref(3, 4),
                          InvalidationEdgeKind.LayoutGeometry,
                          DIRTY_BIT_LAYOUT | DIRTY_BIT_HIT_TEST)
assert_false(decode_dirty_mask(encode_invalidation_edge(e)).ok)
```

</details>

### InvalidationEdgeKind wire discriminants

#### assigns the six architecture edge classes to 0..5 in example order

- assigns the six architecture edge classes to 0..5 in example order


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the six architecture edge classes to 0..5 in example order")
assert_equal(
    invalidation_edge_kind_to_u8(InvalidationEdgeKind.SymbolExport), 0)
assert_equal(
    invalidation_edge_kind_to_u8(InvalidationEdgeKind.CustomProperty), 1)
assert_equal(
    invalidation_edge_kind_to_u8(InvalidationEdgeKind.SelectorMatch), 2)
assert_equal(
    invalidation_edge_kind_to_u8(InvalidationEdgeKind.LayoutGeometry), 3)
assert_equal(
    invalidation_edge_kind_to_u8(InvalidationEdgeKind.FontMetric), 4)
assert_equal(
    invalidation_edge_kind_to_u8(InvalidationEdgeKind.LinkRelocation), 5)
assert_equal(INVALIDATION_EDGE_KIND_MAX, 5)
assert_equal(INVALIDATION_EDGE_KIND_COUNT, 6)
```

</details>

#### round-trips every discriminant and rejects unknown ones

- round-trips every discriminant and rejects unknown ones


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every discriminant and rejects unknown ones")
var v = 0
while v <= INVALIDATION_EDGE_KIND_MAX:
    assert_true(invalidation_edge_kind_valid(v))
    assert_equal(
        invalidation_edge_kind_to_u8(invalidation_edge_kind_from_u8(v)),
        v)
    v = v + 1
assert_false(invalidation_edge_kind_valid(6))
assert_false(invalidation_edge_kind_valid(255))
assert_false(invalidation_edge_kind_valid(-1))
```

</details>

### InvalidationEdge exact bytes

#### encodes the minimal edge to the golden vector

- encodes the minimal edge to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the minimal edge to the golden vector")
val e = invalidation_edge(entity_ref(0, 0), entity_ref(0, 0),
                          InvalidationEdgeKind.SymbolExport,
                          DIRTY_BIT_SOURCE)
assert_equal(wire_to_hex(encode_invalidation_edge(e)), GOLDEN_DEP_MIN)
```

</details>

#### encodes the asymmetric edge to the golden vector

- encodes the asymmetric edge to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the asymmetric edge to the golden vector")
val e = invalidation_edge(entity_ref(1, 2), entity_ref(3, 4),
                          InvalidationEdgeKind.LayoutGeometry,
                          DIRTY_BIT_LAYOUT | DIRTY_BIT_HIT_TEST)
assert_equal(wire_to_hex(encode_invalidation_edge(e)), GOLDEN_DEP_BASIC)
```

</details>

#### encodes the all-ones maximum edge to the golden vector

- encodes the all-ones maximum edge to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the all-ones maximum edge to the golden vector")
val e = invalidation_edge(entity_ref(4294967295, 4294967295),
                          entity_ref(4294967295, 4294967295),
                          InvalidationEdgeKind.LinkRelocation,
                          DIRTY_MASK_KNOWN)
assert_equal(wire_to_hex(encode_invalidation_edge(e)), GOLDEN_DEP_MAX)
```

</details>

#### encodes the font-metric edge to the golden vector

- encodes the font-metric edge to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the font-metric edge to the golden vector")
val e = invalidation_edge(entity_ref(0, 7), entity_ref(0, 9),
                          InvalidationEdgeKind.FontMetric,
                          DIRTY_BIT_INTRINSIC_MEASURE | DIRTY_BIT_LAYOUT
                              | DIRTY_BIT_HIT_TEST)
assert_equal(wire_to_hex(encode_invalidation_edge(e)), GOLDEN_DEP_FONT)
```

</details>

#### emits exactly envelope + 21 bytes

- emits exactly envelope + 21 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exactly envelope + 21 bytes")
val e = invalidation_edge(entity_ref(1, 2), entity_ref(3, 4),
                          InvalidationEdgeKind.FontMetric,
                          DIRTY_BIT_LAYOUT)
assert_equal(INVALIDATION_EDGE_LEN, 21)
assert_equal(encode_invalidation_edge(e).len(),
             WIRE_ENVELOPE_LEN + INVALIDATION_EDGE_LEN)
```

</details>

### InvalidationEdge round trip and rejection

#### round-trips every fixture edge

- round-trips every fixture edge


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every fixture edge")
val es = fixture_edges()
var i = 0
while i < es.len():
    val r = decode_invalidation_edge(encode_invalidation_edge(es[i]))
    assert_true(r.ok)
    assert_true(invalidation_edge_equal(r.value, es[i]))
    i = i + 1
```

</details>

#### refuses an edge that invalidates nothing, on encode and on decode

- refuses an edge that invalidates nothing, on encode and on decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an edge that invalidates nothing, on encode and on decode")
# A zero-mask edge is a graph entry that can never fire; recording one
# is a producer bug that would otherwise sit undetected forever.
val dead = invalidation_edge(entity_ref(1, 1), entity_ref(2, 2),
                             InvalidationEdgeKind.SymbolExport, 0)
assert_false(invalidation_edge_valid(dead))
assert_equal(encode_invalidation_edge(dead).len(), 0)
# Hand-build the same bytes by zeroing a live edge's mask (offsets:
# envelope 0..7, producer 8..15, consumer 16..23, kind 24, mask 25..28).
val live = encode_invalidation_edge(
    invalidation_edge(entity_ref(1, 1), entity_ref(2, 2),
                      InvalidationEdgeKind.SymbolExport,
                      DIRTY_BIT_SOURCE))
assert_false(decode_invalidation_edge(corrupt_byte(live, 25, 0)).ok)
```

</details>

#### hard-rejects an unknown kind discriminant

- hard-rejects an unknown kind discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects an unknown kind discriminant")
val good = encode_invalidation_edge(
    invalidation_edge(entity_ref(1, 2), entity_ref(3, 4),
                      InvalidationEdgeKind.LinkRelocation,
                      DIRTY_BIT_LINK))
assert_false(decode_invalidation_edge(corrupt_byte(good, 24, 6)).ok)
assert_false(decode_invalidation_edge(corrupt_byte(good, 24, 255)).ok)
```

</details>

#### hard-rejects a reserved DirtyMask bit inside an edge

- hard-rejects a reserved DirtyMask bit inside an edge


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects a reserved DirtyMask bit inside an edge")
val good = encode_invalidation_edge(
    invalidation_edge(entity_ref(1, 2), entity_ref(3, 4),
                      InvalidationEdgeKind.FontMetric, DIRTY_BIT_LAYOUT))
# byte 28 carries mask bits 24..31; any set bit there is reserved.
assert_false(decode_invalidation_edge(corrupt_byte(good, 28, 1)).ok)
```

</details>

#### rejects a wrong magic, a wrong version, truncation and trailing bytes

- rejects a wrong magic, a wrong version, truncation and trailing bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a wrong magic, a wrong version, truncation and trailing bytes")
val good = encode_invalidation_edge(
    invalidation_edge(entity_ref(1, 2), entity_ref(3, 4),
                      InvalidationEdgeKind.FontMetric, DIRTY_BIT_LAYOUT))
assert_false(decode_invalidation_edge(corrupt_byte(good, 1, 88)).ok)
assert_false(decode_invalidation_edge(corrupt_byte(good, 4, 9)).ok)
assert_false(
    decode_invalidation_edge(truncated(good, good.len() - 1)).ok)
var longer = good
longer.push(0)
assert_false(decode_invalidation_edge(longer).ok)
```

</details>

#### rejects a DirtyMask buffer offered as an InvalidationEdge

- rejects a DirtyMask buffer offered as an InvalidationEdge


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a DirtyMask buffer offered as an InvalidationEdge")
assert_false(
    decode_invalidation_edge(
        encode_dirty_mask(mask(DIRTY_BIT_SOURCE))).ok)
```

</details>

### InvalidationEdgeBatch exact bytes

#### encodes the empty batch to the golden vector

- encodes the empty batch to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the empty batch to the golden vector")
val off: [u32] = [0]
val none: [InvalidationEdge] = []
assert_equal(
    wire_to_hex(encode_invalidation_edge_batch(
        invalidation_edge_batch_forward(1, 0, off, none))),
    GOLDEN_BATCH_EMPTY)
```

</details>

#### encodes the forward-only batch to the golden vector

- encodes the forward-only batch to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the forward-only batch to the golden vector")
assert_equal(
    wire_to_hex(encode_invalidation_edge_batch(fixture_forward_batch())),
    GOLDEN_BATCH_FORWARD)
```

</details>

#### encodes the batch with a built consumer index to the golden vector

- encodes the batch with a built consumer index to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the batch with a built consumer index to the golden vector")
val b = invalidation_build_reverse(fixture_forward_batch(), 3)
assert_equal(wire_to_hex(encode_invalidation_edge_batch(b)),
             GOLDEN_BATCH_REVERSE)
```

</details>

### InvalidationEdgeBatch structure and traversal

#### builds a deterministic consumer index by counting sort

- builds a deterministic consumer index by counting sort


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a deterministic consumer index by counting sort")
val b = invalidation_build_reverse(fixture_forward_batch(), 3)
assert_true(b.has_reverse)
assert_equal(b.consumer_count, 3)
assert_equal(b.consumer_offsets.len(), 4)
assert_equal(b.consumer_offsets[0], 0)
assert_equal(b.consumer_offsets[1], 0)
assert_equal(b.consumer_offsets[2], 1)
assert_equal(b.consumer_offsets[3], 3)
assert_equal(b.consumer_edges.len(), 3)
assert_equal(b.consumer_edges[0], 0)
assert_equal(b.consumer_edges[1], 1)
assert_equal(b.consumer_edges[2], 2)
# Building it twice yields the same batch — determinism is what lets a
# golden vector freeze the format at all.
assert_true(invalidation_edge_batch_equal(
    b, invalidation_build_reverse(fixture_forward_batch(), 3)))
```

</details>

#### walks forward edges filtered by an interest mask

- walks forward edges filtered by an interest mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("walks forward edges filtered by an interest mask")
val b = fixture_forward_batch()
assert_equal(invalidation_forward_edges(b, 0, DIRTY_MASK_KNOWN).len(), 2)
assert_equal(invalidation_forward_edges(b, 1, DIRTY_MASK_KNOWN).len(), 1)
# Only e0 carries Semantic.
assert_equal(
    invalidation_forward_edges(b, 0, DIRTY_BIT_SEMANTIC).len(), 1)
# Neither of producer 0's edges touches Accessibility.
assert_equal(
    invalidation_forward_edges(b, 0, DIRTY_BIT_ACCESSIBILITY).len(), 0)
```

</details>

#### treats an out-of-range node as a miss, not an error

- treats an out-of-range node as a miss, not an error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats an out-of-range node as a miss, not an error")
val b = fixture_forward_batch()
assert_equal(invalidation_forward_edges(b, 2, DIRTY_MASK_KNOWN).len(), 0)
assert_equal(invalidation_forward_edges(b, -1, DIRTY_MASK_KNOWN).len(), 0)
```

</details>

#### returns nothing in the reverse direction until the index is demanded

- returns nothing in the reverse direction until the index is demanded


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nothing in the reverse direction until the index is demanded")
assert_equal(
    invalidation_reverse_edges(fixture_forward_batch(), 2,
                               DIRTY_MASK_KNOWN).len(), 0)
val b = invalidation_build_reverse(fixture_forward_batch(), 3)
assert_equal(invalidation_reverse_edges(b, 0, DIRTY_MASK_KNOWN).len(), 0)
assert_equal(invalidation_reverse_edges(b, 1, DIRTY_MASK_KNOWN).len(), 1)
assert_equal(invalidation_reverse_edges(b, 2, DIRTY_MASK_KNOWN).len(), 2)
```

</details>

#### rejects a batch whose CSR offsets are ill-formed

- rejects a batch whose CSR offsets are ill-formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a batch whose CSR offsets are ill-formed")
val edges = fixture_edges()
var bad: [u32] = [0, 2]
# Wrong length: a CSR array always has node_count + 1 entries.
assert_false(invalidation_edge_batch_valid(
    invalidation_edge_batch_forward(1, 2, bad, edges)))
var not_zero: [u32] = [1, 2, 3]
assert_false(invalidation_edge_batch_valid(
    invalidation_edge_batch_forward(1, 2, not_zero, edges)))
var decreasing: [u32] = [0, 3, 2]
assert_false(invalidation_edge_batch_valid(
    invalidation_edge_batch_forward(1, 2, decreasing, edges)))
var wrong_end: [u32] = [0, 2, 2]
assert_false(invalidation_edge_batch_valid(
    invalidation_edge_batch_forward(1, 2, wrong_end, edges)))
assert_true(invalidation_edge_batch_valid(fixture_forward_batch()))
```

</details>

### InvalidationEdgeBatch round trip and rejection

#### round-trips the forward-only batch

- round-trips the forward-only batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips the forward-only batch")
val b = fixture_forward_batch()
val r = decode_invalidation_edge_batch(encode_invalidation_edge_batch(b))
assert_true(r.ok)
assert_true(invalidation_edge_batch_equal(r.value, b))
```

</details>

#### round-trips the batch with a consumer index

- round-trips the batch with a consumer index


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips the batch with a consumer index")
val b = invalidation_build_reverse(fixture_forward_batch(), 3)
val r = decode_invalidation_edge_batch(encode_invalidation_edge_batch(b))
assert_true(r.ok)
assert_true(invalidation_edge_batch_equal(r.value, b))
```

</details>

#### refuses to ENCODE an ill-formed batch

- refuses to ENCODE an ill-formed batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to ENCODE an ill-formed batch")
var wrong_end: [u32] = [0, 2, 2]
assert_equal(encode_invalidation_edge_batch(
    invalidation_edge_batch_forward(1, 2, wrong_end,
                                    fixture_edges())).len(), 0)
```

</details>

#### rejects a has_reverse byte outside {0, 1}

- rejects a has_reverse byte outside {0, 1}


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a has_reverse byte outside {0, 1}")
val good = encode_invalidation_edge_batch(fixture_forward_batch())
# Offsets: envelope 0..7, version 8..11, producer_count 12..15,
# edge_count 16..19, has_reverse 20.
assert_false(decode_invalidation_edge_batch(corrupt_byte(good, 20, 2)).ok)
assert_false(
    decode_invalidation_edge_batch(corrupt_byte(good, 20, 255)).ok)
```

</details>

#### rejects a corrupted CSR terminal offset rather than reading a neighbour

- rejects a corrupted CSR terminal offset rather than reading a neighbour


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a corrupted CSR terminal offset rather than reading a neighbour")
val good = encode_invalidation_edge_batch(fixture_forward_batch())
# producer_offsets start at 21; the terminal entry is at 21 + 8 = 29.
assert_false(decode_invalidation_edge_batch(corrupt_byte(good, 29, 2)).ok)
```

</details>

#### rejects a consumer index entry pointing past the forward edge list

- rejects a consumer index entry pointing past the forward edge list


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a consumer index entry pointing past the forward edge list")
val b = invalidation_build_reverse(fixture_forward_batch(), 3)
val good = encode_invalidation_edge_batch(b)
# The consumer_edges run is the last 12 bytes; its final entry starts
# four bytes from the end.
assert_false(
    decode_invalidation_edge_batch(
        corrupt_byte(good, good.len() - 4, 9)).ok)
```

</details>

#### rejects truncation, trailing bytes and a wrong version

- rejects truncation, trailing bytes and a wrong version


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncation, trailing bytes and a wrong version")
val good = encode_invalidation_edge_batch(fixture_forward_batch())
assert_false(
    decode_invalidation_edge_batch(truncated(good, good.len() - 1)).ok)
assert_false(decode_invalidation_edge_batch(truncated(good, 12)).ok)
var longer = good
longer.push(0)
assert_false(decode_invalidation_edge_batch(longer).ok)
assert_false(decode_invalidation_edge_batch(corrupt_byte(good, 4, 7)).ok)
```

</details>

#### rejects a declared count at the u32 maximum on a short buffer

- rejects a declared count at the u32 maximum on a short buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a declared count at the u32 maximum on a short buffer")
# THE WIDTH TRAP. producer_count occupies bytes 12..15. Set it to
# 0xffffffff. Computed at u32 width, `producer_count + 1` wraps to 0 and
# the span check `(count + 1) * 4` passes trivially against ANY buffer,
# admitting a record whose offset array was never present. The decoder
# widens into i64 first, so the span is 17179869184 bytes and the bounds
# check fails as it must.
val good = encode_invalidation_edge_batch(fixture_forward_batch())
var wide = corrupt_byte(good, 12, 255)
wide = corrupt_byte(wide, 13, 255)
wide = corrupt_byte(wide, 14, 255)
wide = corrupt_byte(wide, 15, 255)
assert_false(decode_invalidation_edge_batch(wide).ok)
```

</details>

#### rejects an InvalidationEdge buffer offered as a batch

- rejects an InvalidationEdge buffer offered as a batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an InvalidationEdge buffer offered as a batch")
val e = invalidation_edge(entity_ref(1, 2), entity_ref(3, 4),
                          InvalidationEdgeKind.SelectorMatch,
                          DIRTY_BIT_CASCADE)
assert_false(
    decode_invalidation_edge_batch(encode_invalidation_edge(e)).ok)
```

</details>

### One-hop propagation composes DirtyMask with InvalidationEdge

#### fires only the edges whose invalidation mask the producer touched

- fires only the edges whose invalidation mask the producer touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fires only the edges whose invalidation mask the producer touched")
val b = fixture_forward_batch()
# Producer 0 went dirty in Semantic. Only e0 (Semantic|Hir) cares;
# e1 (ComputedStyle|Layout|Paint) does not intersect it.
val acc = invalidation_propagate_once(b, 0, DIRTY_BIT_SEMANTIC)
assert_equal(acc[0], DIRTY_MASK_EMPTY)
assert_equal(acc[1], DIRTY_BIT_SEMANTIC | DIRTY_BIT_HIR)
assert_equal(acc[2], DIRTY_MASK_EMPTY)
```

</details>

#### carries the edge's whole consequence set, not just the trigger bit

- carries the edge's whole consequence set, not just the trigger bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries the edge's whole consequence set, not just the trigger bit")
val b = fixture_forward_batch()
# ComputedStyle triggers e1, and the consumer acquires all three of
# e1's stages — including Paint, which the producer never set.
val acc = invalidation_propagate_once(b, 0, DIRTY_BIT_COMPUTED_STYLE)
assert_equal(acc[1], DIRTY_MASK_EMPTY)
assert_equal(acc[2], DIRTY_BIT_COMPUTED_STYLE | DIRTY_BIT_LAYOUT
                     | DIRTY_BIT_PAINT)
assert_true(dirty_mask_contains(acc[2], DIRTY_BIT_PAINT))
```

</details>

#### fires nothing when the producer's dirty set misses every edge

- fires nothing when the producer's dirty set misses every edge


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fires nothing when the producer's dirty set misses every edge")
val b = fixture_forward_batch()
val acc = invalidation_propagate_once(b, 0, DIRTY_BIT_ACCESSIBILITY)
assert_equal(acc[1], DIRTY_MASK_EMPTY)
assert_equal(acc[2], DIRTY_MASK_EMPTY)
```

</details>

#### routes a second producer's edge to its own consumer

- routes a second producer's edge to its own consumer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes a second producer's edge to its own consumer")
val b = fixture_forward_batch()
# Producer 1's only edge is e2 (Layout|HitTest), reaching consumer 2.
val acc = invalidation_propagate_once(b, 1, DIRTY_BIT_LAYOUT)
assert_equal(acc[2], DIRTY_BIT_LAYOUT | DIRTY_BIT_HIT_TEST)
```

</details>

#### yields an all-empty result for an out-of-range producer

- yields an all-empty result for an out-of-range producer


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("yields an all-empty result for an out-of-range producer")
val acc = invalidation_propagate_once(fixture_forward_batch(), 7,
                                      DIRTY_MASK_KNOWN)
var i = 0
while i < acc.len():
    assert_equal(acc[i], DIRTY_MASK_EMPTY)
    i = i + 1
```

</details>

### Schema version

#### pins the frozen contract version at 1

- pins the frozen contract version at 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the frozen contract version at 1")
assert_equal(INVALIDATION_SCHEMA_VERSION, 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/invalidation_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DirtyMask wire bit positions, Layout-lane DIRTY_* reconciliation onto the canonical bits, DirtyMask exact bytes, DirtyMask round trip and rejection, InvalidationEdgeKind wire discriminants, InvalidationEdge exact bytes, InvalidationEdge round trip and rejection, InvalidationEdgeBatch exact bytes, InvalidationEdgeBatch structure and traversal, InvalidationEdgeBatch round trip and rejection, One-hop propagation composes DirtyMask with InvalidationEdge, Schema version.
- DirtyMask wire bit positions
- Layout-lane DIRTY_* reconciliation onto the canonical bits
- DirtyMask exact bytes
- DirtyMask round trip and rejection
- InvalidationEdgeKind wire discriminants
- InvalidationEdge exact bytes
- InvalidationEdge round trip and rejection
- InvalidationEdgeBatch exact bytes
- InvalidationEdgeBatch structure and traversal
- InvalidationEdgeBatch round trip and rejection
- One-hop propagation composes DirtyMask with InvalidationEdge
- Schema version

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 57 |
| Active scenarios | 57 |
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

- Canonical SPipe generation for source `96a55f49487341c8fe3ac9e496cd3a70650c28db9ceabe0cbbf51795f6c6c1d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96a55f49487341c8fe3ac9e496cd3a70650c28db9ceabe0cbbf51795f6c6c1d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96a55f49487341c8fe3ac9e496cd3a70650c28db9ceabe0cbbf51795f6c6c1d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/structural/invalidation_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/invalidation_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/invalidation_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/invalidation_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/invalidation_contract_spec.spl:184:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns the 21 architecture stages to bits 0..20 in declaration order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/invalidation_contract_spec.spl:209:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins the vocabulary size, width and the all-known mask' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/invalidation_contract_spec.spl:218:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives each bit from its index and refuses an out-of-range index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
