# Query Contract Specification

> Tests covering QueryDialect wire discriminants, QueryOpKind wire discriminants, QueryDeterminism levels, TagIndexSet wire slot, EntitySetView wire format, QueryOp wire format, QueryOp arena position rules, CaptureSlot and capture schema, QueryProgram wire format, QueryProgram structural rejection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 71 | 71 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Contract Specification

## Scenarios

### QueryDialect wire discriminants

#### assigns the 9 architecture variants to 0..8 in declaration order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- assigns the 9 architecture variants to 0..8 in declaration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("assigns the 9 architecture variants to 0..8 in declaration order")
assert_equal(query_dialect_to_u8(QueryDialect.Syntax), 0)
assert_equal(query_dialect_to_u8(QueryDialect.Semantic), 1)
assert_equal(query_dialect_to_u8(QueryDialect.Mir), 2)
assert_equal(query_dialect_to_u8(QueryDialect.ClangAst), 3)
assert_equal(query_dialect_to_u8(QueryDialect.LlvmIr), 4)
assert_equal(query_dialect_to_u8(QueryDialect.Dom), 5)
assert_equal(query_dialect_to_u8(QueryDialect.CssSelector), 6)
assert_equal(query_dialect_to_u8(QueryDialect.LinkGraph), 7)
assert_equal(query_dialect_to_u8(QueryDialect.LayoutGraph), 8)
```

</details>

#### pins the enum size so a 10th dialect is a version bump

- pins the enum size so a 10th dialect is a version bump


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("pins the enum size so a 10th dialect is a version bump")
assert_equal(QUERY_DIALECT_MAX, 8)
assert_equal(QUERY_DIALECT_COUNT, 9)
```

</details>

#### round-trips every known discriminant

- round-trips every known discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips every known discriminant")
var v = 0
while v <= QUERY_DIALECT_MAX:
    assert_equal(query_dialect_to_u8(query_dialect_from_u8(v)), v)
    v = v + 1
```

</details>

#### hard-rejects an out-of-range dialect discriminant

- hard-rejects an out-of-range dialect discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("hard-rejects an out-of-range dialect discriminant")
assert_true(query_dialect_valid(QUERY_DIALECT_MAX))
assert_false(query_dialect_valid(QUERY_DIALECT_MAX + 1))
assert_false(query_dialect_valid(0 - 1))
```

</details>

### QueryOpKind wire discriminants

#### assigns the 22 architecture operations to 0..21 in declaration order

- assigns the 22 architecture operations to 0..21 in declaration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("assigns the 22 architecture operations to 0..21 in declaration order")
assert_equal(query_op_kind_to_u8(QueryOpKind.SeedAll), 0)
assert_equal(query_op_kind_to_u8(QueryOpKind.SeedTagValue), 3)
assert_equal(query_op_kind_to_u8(QueryOpKind.FilterSourceRange), 7)
assert_equal(query_op_kind_to_u8(QueryOpKind.TraverseMapping), 13)
assert_equal(query_op_kind_to_u8(QueryOpKind.Intersect), 15)
assert_equal(query_op_kind_to_u8(QueryOpKind.NegateWithinUniverse), 18)
assert_equal(query_op_kind_to_u8(QueryOpKind.Capture), 19)
assert_equal(query_op_kind_to_u8(QueryOpKind.Limit), 21)
```

</details>

#### pins the opcode space so a 23rd operation is a version bump

- pins the opcode space so a 23rd operation is a version bump


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("pins the opcode space so a 23rd operation is a version bump")
assert_equal(QUERY_OP_KIND_MAX, 21)
assert_equal(QUERY_OP_KIND_COUNT, 22)
```

</details>

#### round-trips every known opcode

- round-trips every known opcode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips every known opcode")
var v = 0
while v <= QUERY_OP_KIND_MAX:
    assert_equal(query_op_kind_to_u8(query_op_kind_from_u8(v)), v)
    v = v + 1
```

</details>

#### hard-rejects an out-of-range opcode

- hard-rejects an out-of-range opcode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("hard-rejects an out-of-range opcode")
assert_true(query_op_kind_valid(QUERY_OP_KIND_MAX))
assert_false(query_op_kind_valid(QUERY_OP_KIND_MAX + 1))
assert_false(query_op_kind_valid(0 - 1))
```

</details>

#### classifies exactly the four Seed operations as seeds

- classifies exactly the four Seed operations as seeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("classifies exactly the four Seed operations as seeds")
assert_true(query_op_kind_is_seed(QueryOpKind.SeedAll))
assert_true(query_op_kind_is_seed(QueryOpKind.SeedTagValue))
assert_false(query_op_kind_is_seed(QueryOpKind.FilterKind))
assert_false(query_op_kind_is_seed(QueryOpKind.Capture))
```

</details>

#### classifies exactly the three set-algebra operations as binary

- classifies exactly the three set-algebra operations as binary


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("classifies exactly the three set-algebra operations as binary")
assert_true(query_op_kind_is_binary(QueryOpKind.Intersect))
assert_true(query_op_kind_is_binary(QueryOpKind.Union))
assert_true(query_op_kind_is_binary(QueryOpKind.Difference))
# Unary: its second operand is the request universe, not another op.
assert_false(query_op_kind_is_binary(QueryOpKind.NegateWithinUniverse))
```

</details>

### QueryDeterminism levels

#### orders the three derived levels 0..2

- orders the three derived levels 0..2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("orders the three derived levels 0..2")
assert_equal(query_determinism_to_u8(QueryDeterminism.SetDeterministic), 0)
assert_equal(query_determinism_to_u8(QueryDeterminism.OrderDeterministic), 1)
assert_equal(query_determinism_to_u8(QueryDeterminism.CaptureDeterministic), 2)
assert_equal(QUERY_DETERMINISM_MAX, 2)
```

</details>

#### round-trips every known level and rejects the rest

- round-trips every known level and rejects the rest


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips every known level and rejects the rest")
var v = 0
while v <= QUERY_DETERMINISM_MAX:
    assert_equal(query_determinism_to_u8(query_determinism_from_u8(v)), v)
    v = v + 1
assert_false(query_determinism_valid(QUERY_DETERMINISM_MAX + 1))
```

</details>

#### is monotone, so a stronger backend guarantee satisfies a weaker need

- is monotone, so a stronger backend guarantee satisfies a weaker need


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("is monotone, so a stronger backend guarantee satisfies a weaker need")
assert_true(query_determinism_satisfies(
    QueryDeterminism.CaptureDeterministic,
    QueryDeterminism.OrderDeterministic))
assert_true(query_determinism_satisfies(
    QueryDeterminism.OrderDeterministic,
    QueryDeterminism.SetDeterministic))
assert_false(query_determinism_satisfies(
    QueryDeterminism.SetDeterministic,
    QueryDeterminism.OrderDeterministic))
```

</details>

### TagIndexSet wire slot

#### assigns one bit per section 5.3 storage representation

- assigns one bit per section 5.3 storage representation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("assigns one bit per section 5.3 storage representation")
assert_equal(TAG_INDEX_DENSE_MARKER, 1)
assert_equal(TAG_INDEX_SPARSE_RECORDS, 4)
assert_equal(TAG_INDEX_INVERTED_QUERY, 8)
assert_equal(TAG_INDEX_SMALL_SET, 16)
assert_equal(TAG_INDEX_SET_KNOWN, 31)
```

</details>

#### hard-rejects a reserved bit instead of masking it off

- hard-rejects a reserved bit instead of masking it off


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("hard-rejects a reserved bit instead of masking it off")
assert_true(tag_index_set_valid(TAG_INDEX_SET_KNOWN))
assert_true(tag_index_set_valid(TAG_INDEX_SET_EMPTY))
assert_false(tag_index_set_valid(32))
assert_false(tag_index_set_valid(TAG_INDEX_SET_KNOWN + 32))
```

</details>

#### tests membership by bit

- tests membership by bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("tests membership by bit")
val s = TAG_INDEX_SPARSE_RECORDS + TAG_INDEX_INVERTED_QUERY
assert_true(tag_index_set_contains(s, TAG_INDEX_INVERTED_QUERY))
assert_false(tag_index_set_contains(s, TAG_INDEX_DENSE_MARKER))
```

</details>

### EntitySetView wire format

#### encodes the empty view to the exact golden bytes

- encodes the empty view to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes the empty view to the exact golden bytes")
val v = entity_set_view(0, 0, 0, EntitySetOrder.Unordered)
assert_equal(wire_to_hex(encode_entity_set_view(v)), GOLDEN_VIEW_EMPTY)
```

</details>

#### encodes a populated view to the exact golden bytes

- encodes a populated view to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes a populated view to the exact golden bytes")
val v = entity_set_view(1, 2, 3, EntitySetOrder.StableSourceOrder)
assert_equal(wire_to_hex(encode_entity_set_view(v)), GOLDEN_VIEW_BASIC)
```

</details>

#### fixes the view body at 13 bytes with no padding

- fixes the view body at 13 bytes with no padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("fixes the view body at 13 bytes with no padding")
val v = entity_set_view(1, 2, 3, EntitySetOrder.StableSourceOrder)
assert_equal(encode_entity_set_view(v).len(), 8 + ENTITY_SET_VIEW_LEN)
assert_equal(ENTITY_SET_VIEW_LEN, 13)
```

</details>

#### round-trips every EntitySetOrder

- round-trips every EntitySetOrder


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips every EntitySetOrder")
var o = 0
while o <= ENTITY_SET_ORDER_MAX:
    val v = entity_set_view(7, 8, 9, entity_set_order_from_u8(o))
    val r = decode_entity_set_view(encode_entity_set_view(v))
    assert_true(r.ok)
    assert_true(entity_set_view_equal(r.value, v))
    o = o + 1
```

</details>

#### orders the three derived EntitySetOrder levels 0..2

- orders the three derived EntitySetOrder levels 0..2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("orders the three derived EntitySetOrder levels 0..2")
assert_equal(entity_set_order_to_u8(EntitySetOrder.Unordered), 0)
assert_equal(entity_set_order_to_u8(EntitySetOrder.EntityRefOrder), 1)
assert_equal(entity_set_order_to_u8(EntitySetOrder.StableSourceOrder), 2)
assert_false(entity_set_order_valid(ENTITY_SET_ORDER_MAX + 1))
```

</details>

#### hard-rejects an unknown order discriminant

- hard-rejects an unknown order discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("hard-rejects an unknown order discriminant")
val v = entity_set_view(1, 2, 3, EntitySetOrder.Unordered)
val bad = corrupt_byte(encode_entity_set_view(v), 8 + 12, 3)
assert_false(decode_entity_set_view(bad).ok)
```

</details>

#### rejects a view whose run wraps past the u32 index space

- rejects a view whose run wraps past the u32 index space


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a view whose run wraps past the u32 index space")
val v = entity_set_view(0, 0xFFFFFFFF, 2, EntitySetOrder.Unordered)
assert_false(entity_set_view_well_formed(v))
```

</details>

#### rejects a truncated, over-long or cross-typed view buffer

- rejects a truncated, over-long or cross-typed view buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a truncated, over-long or cross-typed view buffer")
val good = encode_entity_set_view(
    entity_set_view(1, 2, 3, EntitySetOrder.Unordered))
assert_false(decode_entity_set_view(truncated(good, good.len() - 1)).ok)
assert_false(decode_entity_set_view(appended(good, 0)).ok)
assert_false(decode_query_op(good).ok)
```

</details>

### QueryOp wire format

#### encodes SeedAll with every absent slot to the exact golden bytes

- encodes SeedAll with every absent slot to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes SeedAll with every absent slot to the exact golden bytes")
val op = query_op_seed(QueryOpKind.SeedAll, QUERY_NO_INPUT,
                       QUERY_NO_CONSTANT)
assert_equal(wire_to_hex(encode_query_op(op)), GOLDEN_OP_SEED_ALL)
```

</details>

#### encodes a binary Intersect to the exact golden bytes

- encodes a binary Intersect to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes a binary Intersect to the exact golden bytes")
val op = query_op_binary(QueryOpKind.Intersect, 0, 1)
assert_equal(wire_to_hex(encode_query_op(op)), GOLDEN_OP_INTERSECT)
```

</details>

#### encodes a constant-carrying TraverseMapping to the exact golden bytes

- encodes a constant-carrying TraverseMapping to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes a constant-carrying TraverseMapping to the exact golden bytes")
val op = query_op_unary(QueryOpKind.TraverseMapping, 1, 0, 2)
assert_equal(wire_to_hex(encode_query_op(op)),
             GOLDEN_OP_TRAVERSE_MAPPING)
```

</details>

#### encodes the maximum opcode to the exact golden bytes

- encodes the maximum opcode to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes the maximum opcode to the exact golden bytes")
val op = query_op_unary(QueryOpKind.Limit, 3, 64, QUERY_NO_CONSTANT)
assert_equal(wire_to_hex(encode_query_op(op)), GOLDEN_OP_LIMIT_MAX)
```

</details>

#### fixes the op word at 18 bytes with no padding

- fixes the op word at 18 bytes with no padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("fixes the op word at 18 bytes with no padding")
assert_equal(QUERY_OP_LEN, 18)
val op = query_op_binary(QueryOpKind.Union, 0, 1)
assert_equal(encode_query_op(op).len(), 8 + QUERY_OP_LEN)
```

</details>

#### round-trips every opcode

- round-trips every opcode


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips every opcode")
var v = 0
while v <= QUERY_OP_KIND_MAX:
    val op = query_op(query_op_kind_from_u8(v), 1, 2, 3, 4)
    val r = decode_query_op(encode_query_op(op))
    assert_true(r.ok)
    assert_true(query_op_equal(r.value, op))
    v = v + 1
```

</details>

#### hard-rejects an unknown opcode byte

- hard-rejects an unknown opcode byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("hard-rejects an unknown opcode byte")
val good = encode_query_op(query_op_binary(QueryOpKind.Union, 0, 1))
assert_false(decode_query_op(corrupt_byte(good, 8,
                                          QUERY_OP_KIND_MAX + 1)).ok)
```

</details>

#### hard-rejects a non-zero reserved byte instead of ignoring it

- hard-rejects a non-zero reserved byte instead of ignoring it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("hard-rejects a non-zero reserved byte instead of ignoring it")
val good = encode_query_op(query_op_binary(QueryOpKind.Union, 0, 1))
assert_true(decode_query_op(good).ok)
assert_false(decode_query_op(corrupt_byte(good, 9, 1)).ok)
```

</details>

#### rejects a truncated, over-long or cross-typed op buffer

- rejects a truncated, over-long or cross-typed op buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a truncated, over-long or cross-typed op buffer")
val good = encode_query_op(query_op_binary(QueryOpKind.Union, 0, 1))
assert_false(decode_query_op(truncated(good, good.len() - 1)).ok)
assert_false(decode_query_op(appended(good, 0)).ok)
assert_false(decode_entity_set_view(good).ok)
```

</details>

#### rejects a wrong schema version rather than negotiating it

- rejects a wrong schema version rather than negotiating it


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a wrong schema version rather than negotiating it")
val good = encode_query_op(query_op_binary(QueryOpKind.Union, 0, 1))
assert_false(decode_query_op(corrupt_byte(good, 4, 2)).ok)
```

</details>

#### rejects a non-zero envelope reserved field

- rejects a non-zero envelope reserved field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a non-zero envelope reserved field")
val good = encode_query_op(query_op_binary(QueryOpKind.Union, 0, 1))
assert_false(decode_query_op(corrupt_byte(good, 6, 1)).ok)
```

</details>

### QueryOp arena position rules

#### accepts a seed only when it carries no input

- accepts a seed only when it carries no input


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("accepts a seed only when it carries no input")
val seed = query_op_seed(QueryOpKind.SeedAll, QUERY_NO_INPUT,
                         QUERY_NO_CONSTANT)
assert_true(query_op_well_formed(seed, 0, 0, 0))
val bad = query_op(QueryOpKind.SeedAll, 0, QUERY_NO_INPUT,
                   QUERY_NO_INPUT, QUERY_NO_CONSTANT)
assert_false(query_op_well_formed(bad, 1, 0, 0))
```

</details>

#### rejects an input that names the op itself or a later op

- rejects an input that names the op itself or a later op


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects an input that names the op itself or a later op")
val self_ref = query_op_unary(QueryOpKind.FilterKind, 2, QUERY_NO_INPUT,
                              QUERY_NO_CONSTANT)
assert_false(query_op_well_formed(self_ref, 2, 0, 0))
assert_false(query_op_well_formed(self_ref, 1, 0, 0))
assert_true(query_op_well_formed(self_ref, 3, 0, 0))
```

</details>

#### rejects a missing input on a non-seed op

- rejects a missing input on a non-seed op


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a missing input on a non-seed op")
val orphan = query_op_unary(QueryOpKind.FilterKind, QUERY_NO_INPUT,
                            QUERY_NO_INPUT, QUERY_NO_CONSTANT)
assert_false(query_op_well_formed(orphan, 1, 0, 0))
```

</details>

#### rejects a second input on an op that is not set algebra

- rejects a second input on an op that is not set algebra


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a second input on an op that is not set algebra")
val bad = query_op(QueryOpKind.FilterKind, 0, 1, QUERY_NO_INPUT,
                   QUERY_NO_CONSTANT)
assert_false(query_op_well_formed(bad, 2, 0, 0))
val good = query_op_binary(QueryOpKind.Difference, 0, 1)
assert_true(query_op_well_formed(good, 2, 0, 0))
```

</details>

#### rejects a constant index past the constant arena

- rejects a constant index past the constant arena


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a constant index past the constant arena")
val bad = query_op_unary(QueryOpKind.FilterTag, 0, QUERY_NO_INPUT, 3)
assert_false(query_op_well_formed(bad, 1, 3, 0))
assert_true(query_op_well_formed(bad, 1, 4, 0))
```

</details>

#### rejects a Capture whose slot index is past the capture schema

- rejects a Capture whose slot index is past the capture schema


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a Capture whose slot index is past the capture schema")
val bad = query_op_unary(QueryOpKind.Capture, 0, 1, QUERY_NO_CONSTANT)
assert_false(query_op_well_formed(bad, 1, 0, 1))
assert_true(query_op_well_formed(bad, 1, 0, 2))
```

</details>

#### rejects a Capture that binds no slot at all

- rejects a Capture that binds no slot at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a Capture that binds no slot at all")
val bad = query_op_unary(QueryOpKind.Capture, 0, QUERY_NO_INPUT,
                         QUERY_NO_CONSTANT)
assert_false(query_op_well_formed(bad, 1, 0, 2))
```

</details>

### CaptureSlot and capture schema

#### encodes an Entity slot to the exact golden bytes

- encodes an Entity slot to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes an Entity slot to the exact golden bytes")
assert_equal(wire_to_hex(encode_capture_slot(
    capture_slot(7, CaptureKind.Entity))),
    GOLDEN_CAPTURE_SLOT_ENTITY)
```

</details>

#### encodes an EntitySet slot to the exact golden bytes

- encodes an EntitySet slot to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes an EntitySet slot to the exact golden bytes")
assert_equal(wire_to_hex(encode_capture_slot(
    capture_slot(0x11223344, CaptureKind.EntitySet))),
    GOLDEN_CAPTURE_SLOT_SET)
```

</details>

#### fixes the slot at 6 bytes with no padding

- fixes the slot at 6 bytes with no padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("fixes the slot at 6 bytes with no padding")
assert_equal(CAPTURE_SLOT_LEN, 6)
assert_equal(encode_capture_slot(
    capture_slot(1, CaptureKind.Entity)).len(), 8 + CAPTURE_SLOT_LEN)
```

</details>

#### round-trips both capture kinds

- round-trips both capture kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips both capture kinds")
var v = 0
while v <= CAPTURE_KIND_MAX:
    val s = capture_slot(5, capture_kind_from_u8(v))
    val r = decode_capture_slot(encode_capture_slot(s))
    assert_true(r.ok)
    assert_true(capture_slot_equal(r.value, s))
    assert_equal(capture_kind_to_u8(r.value.kind), v)
    v = v + 1
```

</details>

#### hard-rejects an unknown capture kind

- hard-rejects an unknown capture kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("hard-rejects an unknown capture kind")
val good = encode_capture_slot(capture_slot(1, CaptureKind.Entity))
assert_false(capture_kind_valid(CAPTURE_KIND_MAX + 1))
assert_false(decode_capture_slot(corrupt_byte(good, 8 + 4, 2)).ok)
```

</details>

#### hard-rejects a non-zero slot reserved byte

- hard-rejects a non-zero slot reserved byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("hard-rejects a non-zero slot reserved byte")
val good = encode_capture_slot(capture_slot(1, CaptureKind.Entity))
assert_false(decode_capture_slot(corrupt_byte(good, 8 + 5, 1)).ok)
```

</details>

#### rejects a schema with two slots of the same name

- rejects a schema with two slots of the same name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a schema with two slots of the same name")
var ss: [CaptureSlot] = []
ss.push(capture_slot(1, CaptureKind.Entity))
ss.push(capture_slot(2, CaptureKind.EntitySet))
assert_true(capture_schema_well_formed(ss))
ss.push(capture_slot(1, CaptureKind.Entity))
assert_false(capture_schema_well_formed(ss))
```

</details>

### QueryProgram wire format

#### encodes the minimal single-seed program to the exact golden bytes

- encodes the minimal single-seed program to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes the minimal single-seed program to the exact golden bytes")
assert_equal(wire_to_hex(encode_query_program(minimal_program())),
             GOLDEN_PROGRAM_MINIMAL)
```

</details>

#### encodes the section 7.6 AOP program to the exact golden bytes

- encodes the section 7.6 AOP program to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes the section 7.6 AOP program to the exact golden bytes")
assert_equal(wire_to_hex(encode_query_program(aop_program())),
             GOLDEN_PROGRAM_AOP)
```

</details>

#### encodes the section 7.7 CSS program to the exact golden bytes

- encodes the section 7.7 CSS program to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("encodes the section 7.7 CSS program to the exact golden bytes")
assert_equal(wire_to_hex(encode_query_program(css_program())),
             GOLDEN_PROGRAM_CSS)
```

</details>

#### lays the header out in 22 bytes ahead of all three arenas

- lays the header out in 22 bytes ahead of all three arenas


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("lays the header out in 22 bytes ahead of all three arenas")
assert_equal(QUERY_PROGRAM_HEADER_LEN, 22)
assert_equal(encode_query_program(minimal_program()).len(),
             8 + QUERY_PROGRAM_HEADER_LEN + QUERY_OP_LEN)
assert_equal(encode_query_program(aop_program()).len(),
             8 + QUERY_PROGRAM_HEADER_LEN + 4 * QUERY_OP_LEN + 3 * 8
                 + CAPTURE_SLOT_LEN)
```

</details>

#### round-trips the AOP program including its u64 constant arena

- round-trips the AOP program including its u64 constant arena


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips the AOP program including its u64 constant arena")
val r = decode_query_program(encode_query_program(aop_program()))
assert_true(r.ok)
assert_true(query_program_equal(r.value, aop_program()))
assert_equal(r.value.constants[0], 0x1122334455667788)
```

</details>

#### round-trips the CSS program including its binary Intersect

- round-trips the CSS program including its binary Intersect


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips the CSS program including its binary Intersect")
val r = decode_query_program(encode_query_program(css_program()))
assert_true(r.ok)
assert_true(query_program_equal(r.value, css_program()))
assert_true(query_op_kind_equal(r.value.ops[2].kind,
                                QueryOpKind.Intersect))
```

</details>

#### round-trips the dialect and determinism header fields

- round-trips the dialect and determinism header fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("round-trips the dialect and determinism header fields")
val r = decode_query_program(encode_query_program(css_program()))
assert_true(r.ok)
assert_true(query_dialect_equal(r.value.dialect,
                                QueryDialect.CssSelector))
assert_equal(query_determinism_to_u8(r.value.determinism), 1)
assert_equal(r.value.index_requirements, TAG_INDEX_INVERTED_QUERY)
```

</details>

#### finds a capture slot by interned name and reports a miss as -1

- finds a capture slot by interned name and reports a miss as -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("finds a capture slot by interned name and reports a miss as -1")
assert_equal(query_program_capture_index(aop_program(), 9), 0)
assert_equal(query_program_capture_index(aop_program(), 10), 0 - 1)
```

</details>

### QueryProgram structural rejection

#### refuses to encode a program with an empty op arena

- refuses to encode a program with an empty op arena


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("refuses to encode a program with an empty op arena")
val ops: [QueryOp] = []
val cs: [u64] = []
val caps: [CaptureSlot] = []
val p = program_of(ops, cs, caps)
assert_false(query_program_valid(p))
assert_equal(encode_query_program(p).len(), 0)
```

</details>

#### refuses to encode a program whose first op is not a seed

- refuses to encode a program whose first op is not a seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("refuses to encode a program whose first op is not a seed")
var ops: [QueryOp] = []
ops.push(query_op_unary(QueryOpKind.FilterKind, QUERY_NO_INPUT,
                        QUERY_NO_INPUT, QUERY_NO_CONSTANT))
val cs: [u64] = []
val caps: [CaptureSlot] = []
assert_false(query_program_valid(program_of(ops, cs, caps)))
```

</details>

#### refuses to encode a program with a forward op reference

- refuses to encode a program with a forward op reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("refuses to encode a program with a forward op reference")
var ops: [QueryOp] = []
ops.push(query_op_seed(QueryOpKind.SeedAll, QUERY_NO_INPUT,
                       QUERY_NO_CONSTANT))
ops.push(query_op_unary(QueryOpKind.FilterKind, 5, QUERY_NO_INPUT,
                        QUERY_NO_CONSTANT))
val cs: [u64] = []
val caps: [CaptureSlot] = []
val p = program_of(ops, cs, caps)
assert_false(query_program_valid(p))
assert_equal(encode_query_program(p).len(), 0)
```

</details>

#### refuses to encode a program with a duplicated capture name

- refuses to encode a program with a duplicated capture name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("refuses to encode a program with a duplicated capture name")
var caps: [CaptureSlot] = []
caps.push(capture_slot(3, CaptureKind.Entity))
caps.push(capture_slot(3, CaptureKind.EntitySet))
val cs: [u64] = []
assert_false(query_program_valid(program_of(minimal_ops(), cs, caps)))
```

</details>

#### refuses to encode a program with a reserved TagIndexSet bit set

- refuses to encode a program with a reserved TagIndexSet bit set


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("refuses to encode a program with a reserved TagIndexSet bit set")
val cs: [u64] = []
val caps: [CaptureSlot] = []
val p = query_program(QueryDialect.Syntax, QUERY_SCHEMA_VERSION,
                      minimal_ops(), cs, caps, 32,
                      QueryDeterminism.SetDeterministic)
assert_false(query_program_valid(p))
assert_equal(encode_query_program(p).len(), 0)
```

</details>

#### hard-rejects an unknown dialect byte on decode

- hard-rejects an unknown dialect byte on decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("hard-rejects an unknown dialect byte on decode")
val good = encode_query_program(minimal_program())
assert_false(decode_query_program(
    corrupt_byte(good, 8, QUERY_DIALECT_MAX + 1)).ok)
```

</details>

#### hard-rejects an unknown determinism byte on decode

- hard-rejects an unknown determinism byte on decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("hard-rejects an unknown determinism byte on decode")
val good = encode_query_program(minimal_program())
assert_false(decode_query_program(
    corrupt_byte(good, 8 + 5, QUERY_DETERMINISM_MAX + 1)).ok)
```

</details>

#### hard-rejects a reserved index-requirement bit on decode

- hard-rejects a reserved index-requirement bit on decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("hard-rejects a reserved index-requirement bit on decode")
val good = encode_query_program(minimal_program())
assert_false(decode_query_program(corrupt_byte(good, 8 + 6, 32)).ok)
```

</details>

#### rejects a declared op count larger than the buffer

- rejects a declared op count larger than the buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a declared op count larger than the buffer")
val good = encode_query_program(minimal_program())
assert_false(decode_query_program(corrupt_byte(good, 8 + 10, 2)).ok)
```

</details>

#### rejects a declared constant count larger than the buffer

- rejects a declared constant count larger than the buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a declared constant count larger than the buffer")
val good = encode_query_program(minimal_program())
assert_false(decode_query_program(corrupt_byte(good, 8 + 14, 9)).ok)
```

</details>

#### rejects a declared capture count larger than the buffer

- rejects a declared capture count larger than the buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a declared capture count larger than the buffer")
val good = encode_query_program(minimal_program())
assert_false(decode_query_program(corrupt_byte(good, 8 + 18, 1)).ok)
```

</details>

#### rejects a decoded arena whose op names a later op

- rejects a decoded arena whose op names a later op


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a decoded arena whose op names a later op")
# Byte 8 + 22 + 2 is op0.input_a. Op0 is a seed, so setting an input
# both breaks the seed rule and would name a nonexistent producer.
val good = encode_query_program(minimal_program())
assert_false(decode_query_program(
    corrupt_byte(good, 8 + QUERY_PROGRAM_HEADER_LEN + 2, 0)).ok)
```

</details>

#### rejects a truncated, over-long or cross-typed program buffer

- rejects a truncated, over-long or cross-typed program buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a truncated, over-long or cross-typed program buffer")
val good = encode_query_program(aop_program())
assert_false(decode_query_program(truncated(good, good.len() - 1)).ok)
assert_false(decode_query_program(appended(good, 0)).ok)
assert_false(decode_query_op(good).ok)
assert_false(decode_query_program(encode_query_op(
    query_op_binary(QueryOpKind.Union, 0, 1))).ok)
```

</details>

#### rejects a wrong program schema version rather than negotiating it

- rejects a wrong program schema version rather than negotiating it


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a wrong program schema version rather than negotiating it")
val good = encode_query_program(minimal_program())
assert_false(decode_query_program(corrupt_byte(good, 4, 2)).ok)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/query_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QueryDialect wire discriminants, QueryOpKind wire discriminants, QueryDeterminism levels, TagIndexSet wire slot, EntitySetView wire format, QueryOp wire format, QueryOp arena position rules, CaptureSlot and capture schema, QueryProgram wire format, QueryProgram structural rejection.
- QueryDialect wire discriminants
- QueryOpKind wire discriminants
- QueryDeterminism levels
- TagIndexSet wire slot
- EntitySetView wire format
- QueryOp wire format
- QueryOp arena position rules
- CaptureSlot and capture schema
- QueryProgram wire format
- QueryProgram structural rejection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 71 |
| Active scenarios | 71 |
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

- Canonical SPipe generation for source `49ed84a9c8e94ad6362922ddabe041770b9ec01a45177853f7a38d5fa44d6dcb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `49ed84a9c8e94ad6362922ddabe041770b9ec01a45177853f7a38d5fa44d6dcb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `49ed84a9c8e94ad6362922ddabe041770b9ec01a45177853f7a38d5fa44d6dcb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/structural/query_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/query_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/query_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/query_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/query_contract_spec.spl:232:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns the 9 architecture variants to 0..8 in declaration order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/query_contract_spec.spl:245:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins the enum size so a 10th dialect is a version bump' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/query_contract_spec.spl:251:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every known discriminant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
