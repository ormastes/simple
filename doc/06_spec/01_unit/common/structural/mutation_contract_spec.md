# Mutation Contract Specification

> Tests covering MutationKind wire discriminants, EntityKindSet derived vocabulary, MutationPhase derived from MutationKind, MutationProducer and ConflictPolicy, fixed-width scalar handling, MutationEffect encoding, MutationOrigin encoding, MutationOp encoding, section 8.4 deterministic conflict order, MutationPlan encoding, MutationCommitReceipt encoding.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 70 | 70 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mutation Contract Specification

## Scenarios

### MutationKind wire discriminants

#### assigns the 26 architecture variants to 0..25 in declaration order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- assigns the 26 architecture variants to 0..25 in declaration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the 26 architecture variants to 0..25 in declaration order")
assert_equal(mutation_kind_to_u8(MutationKind.AddTag), 0)
assert_equal(mutation_kind_to_u8(MutationKind.RemoveTag), 1)
assert_equal(mutation_kind_to_u8(MutationKind.ReplaceSourceRange), 2)
assert_equal(mutation_kind_to_u8(MutationKind.DeleteSyntaxNode), 7)
assert_equal(mutation_kind_to_u8(MutationKind.ReplaceHirNode), 8)
assert_equal(mutation_kind_to_u8(MutationKind.SplitBasicBlock), 12)
assert_equal(mutation_kind_to_u8(MutationKind.ReplaceLlvmInstruction), 13)
assert_equal(mutation_kind_to_u8(MutationKind.MoveDomSubtree), 16)
assert_equal(mutation_kind_to_u8(MutationKind.DeleteCssRule), 21)
assert_equal(mutation_kind_to_u8(MutationKind.ReplaceDeclaration), 22)
assert_equal(mutation_kind_to_u8(MutationKind.AddRelocation), 24)
assert_equal(mutation_kind_to_u8(MutationKind.ChangePlacementHint), 25)
```

</details>

#### pins the enum size so a 27th kind is a version bump

- pins the enum size so a 27th kind is a version bump


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the enum size so a 27th kind is a version bump")
assert_equal(MUTATION_KIND_MAX, 25)
assert_equal(MUTATION_KIND_COUNT, 26)
```

</details>

#### round-trips every known discriminant

- round-trips every known discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every known discriminant")
var v = 0
while v <= MUTATION_KIND_MAX:
    assert_equal(mutation_kind_to_u8(mutation_kind_from_u8(v)), v)
    v = v + 1
```

</details>

#### hard-rejects an out-of-range kind discriminant

- hard-rejects an out-of-range kind discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects an out-of-range kind discriminant")
assert_true(mutation_kind_valid(MUTATION_KIND_MAX))
assert_false(mutation_kind_valid(MUTATION_KIND_MAX + 1))
assert_false(mutation_kind_valid(0 - 1))
```

</details>

### EntityKindSet derived vocabulary

#### assigns one bit per entity class, in section 8.2 order

- assigns one bit per entity class, in section 8.2 order


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns one bit per entity class, in section 8.2 order")
assert_equal(ENTITY_KIND_TAG, 1)
assert_equal(ENTITY_KIND_SOURCE_TEXT, 2)
assert_equal(ENTITY_KIND_SYNTAX_NODE, 4)
assert_equal(ENTITY_KIND_HIR_NODE, 8)
assert_equal(ENTITY_KIND_MIR_INSTRUCTION, 16)
assert_equal(ENTITY_KIND_BASIC_BLOCK, 32)
assert_equal(ENTITY_KIND_LLVM_INSTRUCTION, 64)
assert_equal(ENTITY_KIND_DOM_NODE, 128)
assert_equal(ENTITY_KIND_CSS_RULE, 256)
assert_equal(ENTITY_KIND_DECLARATION, 512)
assert_equal(ENTITY_KIND_LINK_DEFINITION, 1024)
assert_equal(ENTITY_KIND_RELOCATION, 2048)
assert_equal(ENTITY_KIND_PLACEMENT_HINT, 4096)
assert_equal(ENTITY_KIND_SET_KNOWN, 8191)
assert_equal(ENTITY_KIND_SET_BIT_COUNT, 13)
```

</details>

#### hard-rejects a reserved bit rather than masking it off

- hard-rejects a reserved bit rather than masking it off


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects a reserved bit rather than masking it off")
assert_true(entity_kind_set_valid(ENTITY_KIND_SET_EMPTY))
assert_true(entity_kind_set_valid(ENTITY_KIND_SET_KNOWN))
assert_false(entity_kind_set_valid(ENTITY_KIND_SET_KNOWN + 1))
assert_false(entity_kind_set_valid(0 - 1))
```

</details>

#### maps every one of the 26 kinds to exactly one known bit

- maps every one of the 26 kinds to exactly one known bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps every one of the 26 kinds to exactly one known bit")
var v = 0
while v <= MUTATION_KIND_MAX:
    val bit = mutation_kind_target_kind(mutation_kind_from_u8(v))
    assert_true(entity_kind_set_valid(bit))
    assert_true(entity_kind_set_contains(ENTITY_KIND_SET_KNOWN, bit))
    assert_true(bit > 0)
    v = v + 1
```

</details>

#### groups the kinds by the representation they edit

- groups the kinds by the representation they edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("groups the kinds by the representation they edit")
assert_equal(mutation_kind_target_kind(MutationKind.RemoveTag),
             ENTITY_KIND_TAG)
assert_equal(mutation_kind_target_kind(MutationKind.InsertSourceAfter),
             ENTITY_KIND_SOURCE_TEXT)
assert_equal(mutation_kind_target_kind(MutationKind.InsertSyntaxChild),
             ENTITY_KIND_SYNTAX_NODE)
assert_equal(mutation_kind_target_kind(MutationKind.InsertMirAfter),
             ENTITY_KIND_MIR_INSTRUCTION)
assert_equal(mutation_kind_target_kind(MutationKind.SplitBasicBlock),
             ENTITY_KIND_BASIC_BLOCK)
assert_equal(mutation_kind_target_kind(MutationKind.SetDomAttribute),
             ENTITY_KIND_DOM_NODE)
assert_equal(mutation_kind_target_kind(MutationKind.ReplaceCssRule),
             ENTITY_KIND_CSS_RULE)
assert_equal(mutation_kind_target_kind(MutationKind.ReplaceLinkDefinition),
             ENTITY_KIND_LINK_DEFINITION)
assert_equal(mutation_kind_target_kind(MutationKind.ChangePlacementHint),
             ENTITY_KIND_PLACEMENT_HINT)
```

</details>

#### computes disjointness for the ComposeIfDisjoint policy

- computes disjointness for the ComposeIfDisjoint policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes disjointness for the ComposeIfDisjoint policy")
assert_true(entity_kind_set_disjoint(ENTITY_KIND_TAG,
                                     ENTITY_KIND_DOM_NODE))
assert_false(entity_kind_set_disjoint(ENTITY_KIND_SET_KNOWN,
                                      ENTITY_KIND_TAG))
```

</details>

### MutationPhase derived from MutationKind

#### assigns the 4 derived phases to 0..3 in application order

- assigns the 4 derived phases to 0..3 in application order


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the 4 derived phases to 0..3 in application order")
assert_equal(mutation_phase_to_u8(MutationPhase.Remove), 0)
assert_equal(mutation_phase_to_u8(MutationPhase.Replace), 1)
assert_equal(mutation_phase_to_u8(MutationPhase.Insert), 2)
assert_equal(mutation_phase_to_u8(MutationPhase.Restructure), 3)
assert_equal(MUTATION_PHASE_MAX, 3)
assert_equal(MUTATION_PHASE_COUNT, 4)
```

</details>

#### round-trips every known phase discriminant

- round-trips every known phase discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every known phase discriminant")
var v = 0
while v <= MUTATION_PHASE_MAX:
    assert_equal(mutation_phase_to_u8(mutation_phase_from_u8(v)), v)
    v = v + 1
assert_false(mutation_phase_valid(MUTATION_PHASE_MAX + 1))
```

</details>

#### derives a phase for every one of the 26 kinds

- derives a phase for every one of the 26 kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives a phase for every one of the 26 kinds")
var v = 0
while v <= MUTATION_KIND_MAX:
    val p = mutation_phase_to_u8(
        mutation_kind_phase(mutation_kind_from_u8(v)))
    assert_true(mutation_phase_valid(p))
    v = v + 1
```

</details>

#### puts removals first, insertions after the ops they anchor to

- puts removals first, insertions after the ops they anchor to


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("puts removals first, insertions after the ops they anchor to")
assert_equal(mutation_phase_to_u8(
    mutation_kind_phase(MutationKind.RemoveTag)), 0)
assert_equal(mutation_phase_to_u8(
    mutation_kind_phase(MutationKind.DeleteCssRule)), 0)
assert_equal(mutation_phase_to_u8(
    mutation_kind_phase(MutationKind.ReplaceSourceRange)), 1)
assert_equal(mutation_phase_to_u8(
    mutation_kind_phase(MutationKind.ChangePlacementHint)), 1)
assert_equal(mutation_phase_to_u8(
    mutation_kind_phase(MutationKind.AddTag)), 2)
assert_equal(mutation_phase_to_u8(
    mutation_kind_phase(MutationKind.InsertMirBefore)), 2)
assert_equal(mutation_phase_to_u8(
    mutation_kind_phase(MutationKind.SplitBasicBlock)), 3)
assert_equal(mutation_phase_to_u8(
    mutation_kind_phase(MutationKind.MoveDomSubtree)), 3)
```

</details>

### MutationProducer and ConflictPolicy

#### assigns the 6 derived producers to 0..5, catch-all last

- assigns the 6 derived producers to 0..5, catch-all last


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the 6 derived producers to 0..5, catch-all last")
assert_equal(mutation_producer_to_u8(MutationProducer.AopAdvice), 0)
assert_equal(mutation_producer_to_u8(MutationProducer.OptimizerPass), 1)
assert_equal(mutation_producer_to_u8(MutationProducer.CssCascade), 2)
assert_equal(mutation_producer_to_u8(MutationProducer.LinkResolver), 3)
assert_equal(mutation_producer_to_u8(MutationProducer.ClangAdapter), 4)
assert_equal(mutation_producer_to_u8(MutationProducer.Plugin), 5)
assert_equal(MUTATION_PRODUCER_MAX, 5)
assert_equal(MUTATION_PRODUCER_COUNT, 6)
```

</details>

#### round-trips and range-checks every producer discriminant

- round-trips and range-checks every producer discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips and range-checks every producer discriminant")
var v = 0
while v <= MUTATION_PRODUCER_MAX:
    assert_equal(mutation_producer_to_u8(mutation_producer_from_u8(v)),
                 v)
    v = v + 1
assert_false(mutation_producer_valid(MUTATION_PRODUCER_MAX + 1))
```

</details>

#### assigns the 5 architecture conflict policies to 0..4

- assigns the 5 architecture conflict policies to 0..4


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the 5 architecture conflict policies to 0..4")
assert_equal(conflict_policy_to_u8(ConflictPolicy.Reject), 0)
assert_equal(conflict_policy_to_u8(ConflictPolicy.HighestPriorityWins),
             1)
assert_equal(conflict_policy_to_u8(ConflictPolicy.ComposeIfDisjoint), 2)
assert_equal(conflict_policy_to_u8(
    ConflictPolicy.RequeryAfterEarlierMutation), 3)
assert_equal(conflict_policy_to_u8(ConflictPolicy.DomainResolver), 4)
assert_equal(CONFLICT_POLICY_MAX, 4)
assert_equal(CONFLICT_POLICY_COUNT, 5)
```

</details>

#### round-trips and range-checks every policy discriminant

- round-trips and range-checks every policy discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips and range-checks every policy discriminant")
var v = 0
while v <= CONFLICT_POLICY_MAX:
    assert_equal(conflict_policy_to_u8(conflict_policy_from_u8(v)), v)
    v = v + 1
assert_false(conflict_policy_valid(CONFLICT_POLICY_MAX + 1))
```

</details>

#### marks Reject and ComposeIfDisjoint as non-total policies

- marks Reject and ComposeIfDisjoint as non-total policies


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks Reject and ComposeIfDisjoint as non-total policies")
assert_false(conflict_policy_is_total(ConflictPolicy.Reject))
assert_false(conflict_policy_is_total(ConflictPolicy.ComposeIfDisjoint))
assert_true(conflict_policy_is_total(
    ConflictPolicy.HighestPriorityWins))
assert_true(conflict_policy_is_total(
    ConflictPolicy.RequeryAfterEarlierMutation))
assert_true(conflict_policy_is_total(ConflictPolicy.DomainResolver))
```

</details>

### fixed-width scalar handling

#### sign-extends a negative i32 priority through the u32 wire field

- sign-extends a negative i32 priority through the u32 wire field


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sign-extends a negative i32 priority through the u32 wire field")
assert_equal(mutation_i32_to_u32(0 - 1), MUTATION_U32_MAX)
assert_equal(mutation_i32_from_u32(MUTATION_U32_MAX), 0 - 1)
assert_equal(mutation_i32_from_u32(mutation_i32_to_u32(0 - 1)), 0 - 1)
assert_equal(mutation_i32_from_u32(mutation_i32_to_u32(MUTATION_I32_MIN)),
             MUTATION_I32_MIN)
assert_equal(mutation_i32_from_u32(mutation_i32_to_u32(MUTATION_I32_MAX)),
             MUTATION_I32_MAX)
assert_equal(mutation_i32_from_u32(0), 0)
```

</details>

#### range-checks the signed priority field

- range-checks the signed priority field


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("range-checks the signed priority field")
assert_true(mutation_i32_valid(MUTATION_I32_MIN))
assert_true(mutation_i32_valid(MUTATION_I32_MAX))
assert_false(mutation_i32_valid(MUTATION_I32_MAX + 1))
assert_false(mutation_i32_valid(MUTATION_I32_MIN - 1))
```

</details>

#### compares u64 order keys as UNSIGNED even above 2^63

- compares u64 order keys as UNSIGNED even above 2^63


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares u64 order keys as UNSIGNED even above 2^63")
# A u64 above 2^63 is carried as a NEGATIVE i64. A bare `<` would sort
# the whole top half of the space first and make section 8.4's order
# depend on which half a hash landed in.
assert_true(mutation_u64_lt(1, 2))
assert_false(mutation_u64_lt(2, 1))
assert_false(mutation_u64_lt(1, 1))
assert_true(mutation_u64_lt(0x7fffffffffffffff, 0 - 1))
assert_false(mutation_u64_lt(0 - 1, 0x7fffffffffffffff))
assert_true(mutation_u64_lt(0, 0 - 1))
assert_false(mutation_u64_lt(0 - 1, 0))
```

</details>

### MutationEffect encoding

#### pins the record length at 21 bytes

- pins the record length at 21 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the record length at 21 bytes")
assert_equal(MUTATION_EFFECT_LEN, 21)
```

</details>

#### encodes the empty effect to the exact golden bytes

- encodes the empty effect to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the empty effect to the exact golden bytes")
assert_equal(wire_to_hex(encode_mutation_effect(effect_none())),
             GOLDEN_EFFECT_NONE)
```

</details>

#### encodes a MIR effect to the exact golden bytes

- encodes a MIR effect to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a MIR effect to the exact golden bytes")
assert_equal(wire_to_hex(encode_mutation_effect(effect_mir())),
             GOLDEN_EFFECT_MIR)
```

</details>

#### encodes the maximum effect to the exact golden bytes

- encodes the maximum effect to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the maximum effect to the exact golden bytes")
assert_equal(wire_to_hex(encode_mutation_effect(effect_max())),
             GOLDEN_EFFECT_MAX)
```

</details>

#### round-trips every effect shape

- round-trips every effect shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every effect shape")
val a = decode_mutation_effect(encode_mutation_effect(effect_mir()))
assert_true(a.ok)
assert_true(mutation_effect_equal(a.value, effect_mir()))
val b = decode_mutation_effect(encode_mutation_effect(effect_max()))
assert_true(b.ok)
assert_true(mutation_effect_equal(b.value, effect_max()))
```

</details>

#### reads back the four section 8.3 booleans from the flags byte

- reads back the four section 8.3 booleans from the flags byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads back the four section 8.3 booleans from the flags byte")
val r = decode_mutation_effect(encode_mutation_effect(effect_max()))
assert_true(mutation_effect_flag(r.value, EFFECT_FLAG_CONTROL_FLOW))
assert_true(mutation_effect_flag(r.value, EFFECT_FLAG_TYPES))
assert_true(mutation_effect_flag(r.value, EFFECT_FLAG_ABI))
assert_true(mutation_effect_flag(r.value,
                                 EFFECT_FLAG_LAYOUT_GEOMETRY))
val m = decode_mutation_effect(encode_mutation_effect(effect_mir()))
assert_true(mutation_effect_flag(m.value, EFFECT_FLAG_CONTROL_FLOW))
assert_false(mutation_effect_flag(m.value, EFFECT_FLAG_ABI))
```

</details>

#### unions writes, creates and deletes for conflict detection

- unions writes, creates and deletes for conflict detection


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unions writes, creates and deletes for conflict detection")
assert_equal(mutation_effect_mutates(effect_add_tag()),
             ENTITY_KIND_TAG)
assert_equal(mutation_effect_mutates(effect_mir()),
             ENTITY_KIND_MIR_INSTRUCTION)
assert_equal(mutation_effect_mutates(effect_none()), 0)
```

</details>

#### hard-rejects a reserved flags bit on encode and on decode

- hard-rejects a reserved flags bit on encode and on decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects a reserved flags bit on encode and on decode")
val bad = mutation_effect(0, 0, 0, 0, 0, EFFECT_FLAGS_KNOWN + 1)
assert_false(mutation_effect_well_formed(bad))
assert_equal(encode_mutation_effect(bad).len(), 0)
assert_false(effect_flags_valid(EFFECT_FLAGS_KNOWN + 1))
val good = encode_mutation_effect(effect_mir())
val forged = corrupt_byte(good, good.len() - 1, EFFECT_FLAGS_KNOWN + 1)
assert_false(decode_mutation_effect(forged).ok)
```

</details>

#### hard-rejects a reserved EntityKindSet bit on encode and on decode

- hard-rejects a reserved EntityKindSet bit on encode and on decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects a reserved EntityKindSet bit on encode and on decode")
val bad = mutation_effect(ENTITY_KIND_SET_KNOWN + 1, 0, 0, 0, 0, 0)
assert_false(mutation_effect_well_formed(bad))
assert_equal(encode_mutation_effect(bad).len(), 0)
val good = encode_mutation_effect(effect_mir())
# byte 8 is the low byte of `reads`; byte 9 carries bit 8 upward, so
# setting bit 13 means touching the second byte of the field.
val forged = corrupt_byte(good, 9, 0xff)
assert_false(decode_mutation_effect(forged).ok)
```

</details>

#### refuses a truncated, extended, cross-typed or misversioned buffer

- refuses a truncated, extended, cross-typed or misversioned buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a truncated, extended, cross-typed or misversioned buffer")
val good = encode_mutation_effect(effect_mir())
assert_false(decode_mutation_effect(truncated(good,
                                              good.len() - 1)).ok)
assert_false(decode_mutation_effect(appended(good, 0)).ok)
assert_false(decode_mutation_effect(corrupt_byte(good, 0, 0x54)).ok)
assert_false(decode_mutation_effect(corrupt_byte(good, 4, 2)).ok)
assert_false(decode_mutation_effect(corrupt_byte(good, 6, 1)).ok)
assert_false(decode_mutation_origin(good).ok)
```

</details>

### MutationOrigin encoding

#### pins the record length at 9 bytes

- pins the record length at 9 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the record length at 9 bytes")
assert_equal(MUTATION_ORIGIN_LEN, 9)
```

</details>

#### encodes an AOP advice origin to the exact golden bytes

- encodes an AOP advice origin to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes an AOP advice origin to the exact golden bytes")
assert_equal(wire_to_hex(encode_mutation_origin(origin_aop())),
             GOLDEN_ORIGIN_AOP)
```

</details>

#### encodes the maximum producer origin to the exact golden bytes

- encodes the maximum producer origin to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the maximum producer origin to the exact golden bytes")
assert_equal(wire_to_hex(encode_mutation_origin(origin_plugin_max())),
             GOLDEN_ORIGIN_PLUGIN_MAX)
```

</details>

#### round-trips both origin shapes

- round-trips both origin shapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips both origin shapes")
val a = decode_mutation_origin(encode_mutation_origin(origin_aop()))
assert_true(a.ok)
assert_true(mutation_origin_equal(a.value, origin_aop()))
val b = decode_mutation_origin(
    encode_mutation_origin(origin_plugin_max()))
assert_true(b.ok)
assert_true(mutation_origin_equal(b.value, origin_plugin_max()))
```

</details>

#### hard-rejects an unknown producer discriminant

- hard-rejects an unknown producer discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects an unknown producer discriminant")
val good = encode_mutation_origin(origin_aop())
val forged = corrupt_byte(good, 8, MUTATION_PRODUCER_MAX + 1)
assert_false(decode_mutation_origin(forged).ok)
```

</details>

#### refuses a truncated, extended or cross-typed buffer

- refuses a truncated, extended or cross-typed buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a truncated, extended or cross-typed buffer")
val good = encode_mutation_origin(origin_aop())
assert_false(decode_mutation_origin(truncated(good,
                                              good.len() - 1)).ok)
assert_false(decode_mutation_origin(appended(good, 0)).ok)
assert_false(decode_mutation_effect(good).ok)
```

</details>

### MutationOp encoding

#### pins the record length at 105 bytes

- pins the record length at 105 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the record length at 105 bytes")
assert_equal(MUTATION_OP_LEN, 105)
```

</details>

#### encodes the AddTag op to the exact golden bytes

- encodes the AddTag op to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the AddTag op to the exact golden bytes")
assert_equal(wire_to_hex(encode_mutation_op(op_add_tag())),
             GOLDEN_OP_ADD_TAG)
```

</details>

#### encodes the maximum op to the exact golden bytes

- encodes the maximum op to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the maximum op to the exact golden bytes")
assert_equal(wire_to_hex(encode_mutation_op(op_max())), GOLDEN_OP_MAX)
```

</details>

#### round-trips both op shapes, including a negative priority

- round-trips both op shapes, including a negative priority


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips both op shapes, including a negative priority")
val a = decode_mutation_op(encode_mutation_op(op_add_tag()))
assert_true(a.ok)
assert_true(mutation_op_equal(a.value, op_add_tag()))
assert_equal(a.value.priority, 10)
val b = decode_mutation_op(encode_mutation_op(op_max()))
assert_true(b.ok)
assert_true(mutation_op_equal(b.value, op_max()))
assert_equal(b.value.priority, 0 - 1)
```

</details>

#### derives the phase from the kind rather than trusting the caller

- derives the phase from the kind rather than trusting the caller


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives the phase from the kind rather than trusting the caller")
assert_equal(mutation_phase_to_u8(op_add_tag().phase), 2)
assert_equal(mutation_phase_to_u8(op_max().phase), 1)
```

</details>

#### distinguishes an absent payload and precondition from index zero

- distinguishes an absent payload and precondition from index zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes an absent payload and precondition from index zero")
assert_true(mutation_op_has_payload(op_add_tag()))
assert_false(mutation_op_has_precondition(op_add_tag()))
assert_false(mutation_op_has_payload(op_max()))
assert_true(mutation_op_has_precondition(op_max()))
assert_equal(MUTATION_NO_PAYLOAD, MUTATION_U32_MAX)
assert_equal(MUTATION_NO_PRECONDITION, MUTATION_U32_MAX)
```

</details>

#### hard-rejects an op whose effect hides what it changes

- hard-rejects an op whose effect hides what it changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects an op whose effect hides what it changes")
# Section 8.3 makes the effect summary what conflict detection runs on,
# so an op that edits a tag while claiming to change nothing is
# invisible to conflict detection and still mutates the snapshot.
val blind = mutation_op(MutationKind.AddTag, target_a(), revision_a(),
                        5, MUTATION_NO_PRECONDITION, origin_aop(), 10,
                        1, mutation_effect_none())
assert_false(mutation_op_well_formed(blind))
assert_equal(encode_mutation_op(blind).len(), 0)

# ... and one that names a DIFFERENT kind than its target is refused
# too, so the check cannot be satisfied by any non-empty effect.
val wrong = mutation_op(MutationKind.AddTag, target_a(), revision_a(),
                        5, MUTATION_NO_PRECONDITION, origin_aop(), 10,
                        1,
                        mutation_effect(0, ENTITY_KIND_DOM_NODE, 0, 0,
                                        0, 0))
assert_false(mutation_op_well_formed(wrong))
assert_equal(encode_mutation_op(wrong).len(), 0)
```

</details>

#### hard-rejects a forged phase byte that disagrees with the kind

- hard-rejects a forged phase byte that disagrees with the kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects a forged phase byte that disagrees with the kind")
val good = encode_mutation_op(op_add_tag())
# byte 8 = envelope(8) + 0 -> kind; byte 9 -> phase.
val forged = corrupt_byte(good, 9, 0)
assert_false(decode_mutation_op(forged).ok)
val forged_max = corrupt_byte(good, 9, MUTATION_PHASE_MAX)
assert_false(decode_mutation_op(forged_max).ok)
```

</details>

#### hard-rejects an unknown kind discriminant and a non-zero reserved byte

- hard-rejects an unknown kind discriminant and a non-zero reserved byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects an unknown kind discriminant and a non-zero reserved byte")
val good = encode_mutation_op(op_add_tag())
assert_false(decode_mutation_op(corrupt_byte(good, 8,
                                             MUTATION_KIND_MAX + 1)).ok)
assert_false(decode_mutation_op(corrupt_byte(good, 10, 1)).ok)
```

</details>

#### refuses a truncated, extended, cross-typed or misversioned buffer

- refuses a truncated, extended, cross-typed or misversioned buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a truncated, extended, cross-typed or misversioned buffer")
val good = encode_mutation_op(op_add_tag())
assert_false(decode_mutation_op(truncated(good, good.len() - 1)).ok)
assert_false(decode_mutation_op(appended(good, 0)).ok)
assert_false(decode_mutation_op(corrupt_byte(good, 1, 0x51)).ok)
assert_false(decode_mutation_op(corrupt_byte(good, 4, 2)).ok)
assert_false(decode_mutation_op(corrupt_byte(good, 7, 1)).ok)
assert_false(decode_mutation_plan(good).ok)
```

</details>

### section 8.4 deterministic conflict order

#### orders by target entity first, in wire-field order

- orders by target entity first, in wire-field order


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders by target entity first, in wire-field order")
assert_true(mutation_entity_key_before(target_a(), target_max()))
assert_false(mutation_entity_key_before(target_max(), target_a()))
assert_false(mutation_entity_key_before(target_a(), target_a()))
```

</details>

#### orders by phase second, ahead of priority

- orders by phase second, ahead of priority


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders by phase second, ahead of priority")
# A Remove at the LOWEST priority still precedes an Insert at the
# highest, because phase is key 2 and priority is only key 3.
val remove_low = mutation_op(MutationKind.RemoveTag, target_a(),
                             revision_a(), 0, MUTATION_NO_PRECONDITION,
                             origin_aop(), MUTATION_I32_MIN, 0,
                             mutation_effect(0, 0, 0, ENTITY_KIND_TAG,
                                             0, 0))
val insert_high = mutation_op(MutationKind.AddTag, target_a(),
                              revision_a(), 0,
                              MUTATION_NO_PRECONDITION, origin_aop(),
                              MUTATION_I32_MAX, 0, effect_add_tag())
assert_true(mutation_op_before(remove_low, insert_high))
assert_false(mutation_op_before(insert_high, remove_low))
```

</details>

#### sorts priority DESCENDING so HighestPriorityWins comes first

- sorts priority DESCENDING so HighestPriorityWins comes first


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts priority DESCENDING so HighestPriorityWins comes first")
val low = mutation_op(MutationKind.AddTag, target_a(), revision_a(), 0,
                      MUTATION_NO_PRECONDITION, origin_aop(), 1, 0,
                      effect_add_tag())
val high = mutation_op(MutationKind.AddTag, target_a(), revision_a(), 0,
                       MUTATION_NO_PRECONDITION, origin_aop(), 2, 0,
                       effect_add_tag())
assert_true(mutation_op_before(high, low))
assert_false(mutation_op_before(low, high))

# And a NEGATIVE priority sorts last, which is the case a u32 read of
# the priority field would silently invert.
val negative = mutation_op(MutationKind.AddTag, target_a(),
                           revision_a(), 0, MUTATION_NO_PRECONDITION,
                           origin_aop(), 0 - 5, 0, effect_add_tag())
assert_true(mutation_op_before(low, negative))
assert_false(mutation_op_before(negative, low))
```

</details>

#### falls through stable name, then source order, then stable ordinal

- falls through stable name, then source order, then stable ordinal


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls through stable name, then source order, then stable ordinal")
val by_name = mutation_op(MutationKind.AddTag, target_a(), revision_a(),
                          0, MUTATION_NO_PRECONDITION,
                          mutation_origin(MutationProducer.AopAdvice,
                                          0x11223345, 7),
                          10, 1, effect_add_tag())
assert_true(mutation_op_before(op_add_tag(), by_name))

val by_source = mutation_op(MutationKind.AddTag, target_a(),
                            revision_a(), 0, MUTATION_NO_PRECONDITION,
                            mutation_origin(MutationProducer.AopAdvice,
                                            0x11223344, 8),
                            10, 1, effect_add_tag())
assert_true(mutation_op_before(op_add_tag(), by_source))

assert_true(mutation_op_before(op_add_tag(), op_add_tag_next()))
assert_false(mutation_op_before(op_add_tag_next(), op_add_tag()))
```

</details>

#### is strict, so an order-ambiguous pair is detectable

- is strict, so an order-ambiguous pair is detectable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is strict, so an order-ambiguous pair is detectable")
assert_true(mutation_op_order_equal(op_add_tag(), op_add_tag()))
assert_false(mutation_op_order_equal(op_add_tag(), op_add_tag_next()))
```

</details>

#### detects two ops that change overlapping kinds on one target

- detects two ops that change overlapping kinds on one target


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects two ops that change overlapping kinds on one target")
assert_true(mutation_op_conflicts_with(op_add_tag(),
                                       op_add_tag_next()))
assert_false(mutation_op_conflicts_with(op_add_tag(), op_max()))
assert_equal(mutation_plan_conflict_count(plan_ordered_pair()), 1)
assert_equal(mutation_plan_conflict_count(plan_single_max()), 0)
```

</details>

### MutationPlan encoding

#### pins the plan header length at 9 bytes

- pins the plan header length at 9 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the plan header length at 9 bytes")
assert_equal(MUTATION_PLAN_HEADER_LEN, 9)
```

</details>

#### encodes a single-op maximum plan to the exact golden bytes

- encodes a single-op maximum plan to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a single-op maximum plan to the exact golden bytes")
assert_equal(wire_to_hex(encode_mutation_plan(plan_single_max())),
             GOLDEN_PLAN_SINGLE_MAX)
```

</details>

#### encodes an ordered two-op plan to the exact golden bytes

- encodes an ordered two-op plan to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes an ordered two-op plan to the exact golden bytes")
assert_equal(wire_to_hex(encode_mutation_plan(plan_ordered_pair())),
             GOLDEN_PLAN_ORDERED_PAIR)
```

</details>

#### round-trips both plan shapes

- round-trips both plan shapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips both plan shapes")
val a = decode_mutation_plan(encode_mutation_plan(plan_single_max()))
assert_true(a.ok)
assert_true(mutation_plan_equal(a.value, plan_single_max()))
val b = decode_mutation_plan(encode_mutation_plan(plan_ordered_pair()))
assert_true(b.ok)
assert_true(mutation_plan_equal(b.value, plan_ordered_pair()))
assert_equal(b.value.ops.len(), 2)
```

</details>

#### makes an out-of-order plan unrepresentable on the wire

- makes an out-of-order plan unrepresentable on the wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes an out-of-order plan unrepresentable on the wire")
# This is the whole point of the group. Section 30.5 requires that
# ordering be deterministic and that conflicts never depend on thread
# scheduling; a plan stored out of section 8.4 order commits a
# DIFFERENT snapshot depending on which evaluator walked it.
assert_false(mutation_plan_ordered(plan_swapped_pair()))
assert_false(mutation_plan_valid(plan_swapped_pair()))
assert_equal(encode_mutation_plan(plan_swapped_pair()).len(), 0)
```

</details>

#### refuses a plan containing an order-ambiguous duplicate pair

- refuses a plan containing an order-ambiguous duplicate pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a plan containing an order-ambiguous duplicate pair")
var ops: [MutationOp] = []
ops.push(op_add_tag())
ops.push(op_add_tag())
val dup = mutation_plan(ConflictPolicy.Reject, MUTATION_SCHEMA_VERSION,
                        ops)
assert_false(mutation_plan_ordered(dup))
assert_equal(encode_mutation_plan(dup).len(), 0)
```

</details>

#### refuses an empty plan on encode

- refuses an empty plan on encode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an empty plan on encode")
val none: [MutationOp] = []
val empty = mutation_plan(ConflictPolicy.Reject,
                          MUTATION_SCHEMA_VERSION, none)
assert_false(mutation_plan_valid(empty))
assert_equal(encode_mutation_plan(empty).len(), 0)
```

</details>

#### hard-rejects an unknown conflict policy discriminant

- hard-rejects an unknown conflict policy discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects an unknown conflict policy discriminant")
val good = encode_mutation_plan(plan_ordered_pair())
assert_false(decode_mutation_plan(corrupt_byte(good, 8,
                                               CONFLICT_POLICY_MAX + 1)).ok)
```

</details>

#### refuses a truncated, extended, cross-typed or overstated buffer

- refuses a truncated, extended, cross-typed or overstated buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a truncated, extended, cross-typed or overstated buffer")
val good = encode_mutation_plan(plan_ordered_pair())
assert_false(decode_mutation_plan(truncated(good, good.len() - 1)).ok)
assert_false(decode_mutation_plan(appended(good, 0)).ok)
assert_false(decode_mutation_plan(corrupt_byte(good, 2, 0x51)).ok)
assert_false(decode_mutation_plan(corrupt_byte(good, 4, 2)).ok)
assert_false(decode_mutation_op(good).ok)
# An op_count larger than the buffer holds must be refused BEFORE any
# allocation against the declared count.
assert_false(decode_mutation_plan(corrupt_byte(good, 13, 0xff)).ok)
```

</details>

### MutationCommitReceipt encoding

#### pins the record length at 104 bytes

- pins the record length at 104 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the record length at 104 bytes")
assert_equal(MUTATION_RECEIPT_LEN, 104)
```

</details>

#### encodes an applied-commit receipt to the exact golden bytes

- encodes an applied-commit receipt to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes an applied-commit receipt to the exact golden bytes")
assert_equal(wire_to_hex(encode_mutation_receipt(receipt_applied())),
             GOLDEN_RECEIPT_APPLIED)
```

</details>

#### encodes a failed-validation receipt to the exact golden bytes

- encodes a failed-validation receipt to the exact golden bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a failed-validation receipt to the exact golden bytes")
assert_equal(wire_to_hex(encode_mutation_receipt(receipt_no_op())),
             GOLDEN_RECEIPT_NO_OP)
```

</details>

#### round-trips both receipt shapes

- round-trips both receipt shapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips both receipt shapes")
val a = decode_mutation_receipt(
    encode_mutation_receipt(receipt_applied()))
assert_true(a.ok)
assert_true(mutation_receipt_equal(a.value, receipt_applied()))
val b = decode_mutation_receipt(
    encode_mutation_receipt(receipt_no_op()))
assert_true(b.ok)
assert_true(mutation_receipt_equal(b.value, receipt_no_op()))
```

</details>

#### refuses a receipt reporting more conflicts than skips

- refuses a receipt reporting more conflicts than skips


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a receipt reporting more conflicts than skips")
val bad = mutation_commit_receipt(snapshot_at(7), snapshot_at(8),
                                  hash128(0, 0), 4, 3, 1, 3)
assert_false(mutation_receipt_well_formed(bad))
assert_equal(encode_mutation_receipt(bad).len(), 0)
```

</details>

#### refuses a no-op commit that claims a different output snapshot

- refuses a no-op commit that claims a different output snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a no-op commit that claims a different output snapshot")
# Section 30.5: failed validation leaves the original snapshot
# unchanged.
val bad = mutation_commit_receipt(snapshot_at(7), snapshot_at(8),
                                  hash128(0, 0), 4, 0, 4, 4)
assert_false(mutation_receipt_well_formed(bad))
assert_equal(encode_mutation_receipt(bad).len(), 0)
```

</details>

#### refuses an applied commit whose output does not supersede its input

- refuses an applied commit whose output does not supersede its input


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an applied commit whose output does not supersede its input")
val same = mutation_commit_receipt(snapshot_at(7), snapshot_at(7),
                                   hash128(0, 0), 4, 3, 1, 1)
assert_false(mutation_receipt_well_formed(same))
assert_equal(encode_mutation_receipt(same).len(), 0)
val backwards = mutation_commit_receipt(snapshot_at(8),
                                        snapshot_at(7),
                                        hash128(0, 0), 4, 3, 1, 1)
assert_false(mutation_receipt_well_formed(backwards))
assert_equal(encode_mutation_receipt(backwards).len(), 0)
```

</details>

#### refuses a truncated, extended, cross-typed or misversioned buffer

- refuses a truncated, extended, cross-typed or misversioned buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a truncated, extended, cross-typed or misversioned buffer")
val good = encode_mutation_receipt(receipt_applied())
assert_false(decode_mutation_receipt(truncated(good,
                                               good.len() - 1)).ok)
assert_false(decode_mutation_receipt(appended(good, 0)).ok)
assert_false(decode_mutation_receipt(corrupt_byte(good, 3, 0x50)).ok)
assert_false(decode_mutation_receipt(corrupt_byte(good, 4, 2)).ok)
assert_false(decode_mutation_receipt(corrupt_byte(good, 6, 1)).ok)
assert_false(decode_mutation_plan(good).ok)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/mutation_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MutationKind wire discriminants, EntityKindSet derived vocabulary, MutationPhase derived from MutationKind, MutationProducer and ConflictPolicy, fixed-width scalar handling, MutationEffect encoding, MutationOrigin encoding, MutationOp encoding, section 8.4 deterministic conflict order, MutationPlan encoding, MutationCommitReceipt encoding.
- MutationKind wire discriminants
- EntityKindSet derived vocabulary
- MutationPhase derived from MutationKind
- MutationProducer and ConflictPolicy
- fixed-width scalar handling
- MutationEffect encoding
- MutationOrigin encoding
- MutationOp encoding
- section 8.4 deterministic conflict order
- MutationPlan encoding
- MutationCommitReceipt encoding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 70 |
| Active scenarios | 70 |
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

- Canonical SPipe generation for source `7876bc5f20976a00d97d7392ca78ee01ca6c0f7fa150bf732d36fc2c0f8c7891`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7876bc5f20976a00d97d7392ca78ee01ca6c0f7fa150bf732d36fc2c0f8c7891`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7876bc5f20976a00d97d7392ca78ee01ca6c0f7fa150bf732d36fc2c0f8c7891`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/structural/mutation_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/mutation_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/mutation_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/mutation_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/mutation_contract_spec.spl:290:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns the 26 architecture variants to 0..25 in declaration order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/mutation_contract_spec.spl:306:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins the enum size so a 27th kind is a version bump' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/mutation_contract_spec.spl:312:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every known discriminant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
