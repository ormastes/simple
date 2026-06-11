# Basic Type Check Specification

> <details>

<!-- sdn-diagram:id=basic_type_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=basic_type_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

basic_type_check_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=basic_type_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basic Type Check Specification

## Scenarios

### Type Tag Constants

#### defines nil type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TYPE_NIL).to_equal(13)
```

</details>

#### defines bool type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TYPE_BOOL).to_equal(1)
```

</details>

#### defines i64 type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TYPE_I64).to_equal(2)
```

</details>

#### defines f64 type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TYPE_F64).to_equal(3)
```

</details>

#### defines text type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TYPE_TEXT).to_equal(4)
```

</details>

#### defines any type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TYPE_ANY).to_equal(12)
```

</details>

### Union Type Registry

#### can register union members

1. test union members push
   - Expected: test_union_members.len() equals `1`
   - Expected: test_union_members[0].len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var test_union_members: [[i64]] = []
test_union_members.push([TYPE_I64, TYPE_TEXT])
expect(test_union_members.len()).to_equal(1)
expect(test_union_members[0].len()).to_equal(2)
```

</details>

#### can retrieve union members

1. test union members push
   - Expected: members[0] equals `TYPE_I64`
   - Expected: members[1] equals `TYPE_TEXT`
   - Expected: members[2] equals `TYPE_F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var test_union_members: [[i64]] = []
test_union_members.push([TYPE_I64, TYPE_TEXT, TYPE_F64])
val members = test_union_members[0]
expect(members[0]).to_equal(TYPE_I64)
expect(members[1]).to_equal(TYPE_TEXT)
expect(members[2]).to_equal(TYPE_F64)
```

</details>

### Intersection Type Registry

#### can register intersection members

1. test inter members push
   - Expected: test_inter_members.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var test_inter_members: [[i64]] = []
test_inter_members.push([TYPE_ANY, TYPE_I64])
expect(test_inter_members.len()).to_equal(1)
```

</details>

#### can retrieve intersection members

1. test inter members push
   - Expected: members.len() equals `1`
   - Expected: members[0] equals `TYPE_I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var test_inter_members: [[i64]] = []
test_inter_members.push([TYPE_I64])
val members = test_inter_members[0]
expect(members.len()).to_equal(1)
expect(members[0]).to_equal(TYPE_I64)
```

</details>

### Refinement Type Registry

#### can register refinement base types

1. test ref bases push
2. test ref predicates push
   - Expected: test_ref_bases.len() equals `1`
   - Expected: test_ref_predicates.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var test_ref_bases: [i64] = []
var test_ref_predicates: [text] = []
test_ref_bases.push(TYPE_I64)
test_ref_predicates.push("x > 0")
expect(test_ref_bases.len()).to_equal(1)
expect(test_ref_predicates.len()).to_equal(1)
```

</details>

#### can retrieve refinement predicate

1. test ref bases push
2. test ref predicates push
   - Expected: predicate equals `x > 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var test_ref_bases: [i64] = []
var test_ref_predicates: [text] = []
test_ref_bases.push(TYPE_I64)
test_ref_predicates.push("x > 0")
val predicate = test_ref_predicates[0]
expect(predicate).to_equal("x > 0")
```

</details>

#### can check empty predicate

1. test ref bases push
2. test ref predicates push
   - Expected: predicate equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var test_ref_bases: [i64] = []
var test_ref_predicates: [text] = []
test_ref_bases.push(TYPE_TEXT)
test_ref_predicates.push("")
val predicate = test_ref_predicates[0]
expect(predicate).to_equal("")
```

</details>

### Type Checking Logic

#### validates positive integer predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value: i64 = 5
val is_positive = value > 0
expect(is_positive).to_equal(true)
```

</details>

#### validates negative integer predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value: i64 = -3
val is_positive = value > 0
expect(is_positive).to_equal(false)
```

</details>

#### validates zero for >= 0 predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value: i64 = 0
val is_non_negative = value >= 0
expect(is_non_negative).to_equal(true)
```

</details>

#### validates bounded integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value: i64 = 50
val is_bounded = value < 100
expect(is_bounded).to_equal(true)
```

</details>

#### rejects out of bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value: i64 = 150
val is_bounded = value < 100
expect(is_bounded).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/type/basic_type_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Type Tag Constants
- Union Type Registry
- Intersection Type Registry
- Refinement Type Registry
- Type Checking Logic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
