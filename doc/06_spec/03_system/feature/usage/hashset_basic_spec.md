# HashSet Basic Operations

> Tests HashSet basic operations using a self-contained implementation. Covers set creation and initialization, element insertion with deduplication, membership testing via contains and remove, collection mutations like clear, and array conversion via to_vec.

<!-- sdn-diagram:id=hashset_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hashset_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hashset_basic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hashset_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HashSet Basic Operations

Tests HashSet basic operations using a self-contained implementation. Covers set creation and initialization, element insertion with deduplication, membership testing via contains and remove, collection mutations like clear, and array conversion via to_vec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | In Progress |
| Source | `test/03_system/feature/usage/hashset_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests HashSet basic operations using a self-contained implementation. Covers set creation
and initialization, element insertion with deduplication, membership testing via contains
and remove, collection mutations like clear, and array conversion via to_vec.

## Scenarios

### HashSet basic operations

#### Creation and insertion

#### creates new HashSet

1. var set = HashSet new
   - Expected: set.len() equals `0`
   - Expected: set.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var set = HashSet.new()
expect(set.len()).to_equal(0)
expect(set.is_empty()).to_equal(true)
```

</details>

#### inserts elements

1. var set = HashSet new
2. set insert
3. set insert
4. set insert
   - Expected: set.len() equals `3`
   - Expected: set contains `apple`
   - Expected: set contains `banana`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var set = HashSet.new()
set.insert("apple")
set.insert("banana")
set.insert("cherry")

expect(set.len()).to_equal(3)
expect(set.contains("apple")).to_equal(true)
expect(set.contains("banana")).to_equal(true)
```

</details>

#### handles duplicate insertions

1. var set = HashSet new
2. set insert
3. set insert
4. set insert
   - Expected: set.len() equals `2`
   - Expected: set contains `cat`
   - Expected: set contains `dog`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var set = HashSet.new()
set.insert("cat")
set.insert("dog")
set.insert("cat")
expect(set.len()).to_equal(2)
expect(set.contains("cat")).to_equal(true)
expect(set.contains("dog")).to_equal(true)
```

</details>

#### Membership testing

#### checks if element exists

1. var set = HashSet new
2. set insert
   - Expected: set contains `exists`
   - Expected: set does not contain `missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var set = HashSet.new()
set.insert("exists")

expect(set.contains("exists")).to_equal(true)
expect(set.contains("missing")).to_equal(false)
```

</details>

#### removes elements

1. var set = HashSet new
2. set insert
   - Expected: removed is true
   - Expected: set does not contain `temp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var set = HashSet.new()
set.insert("temp")

val removed = set.remove("temp")
expect(removed).to_equal(true)
expect(set.contains("temp")).to_equal(false)
```

</details>

#### Collection operations

#### clears all elements

1. var set = HashSet new
2. set insert
3. set insert
4. set insert
5. set clear
   - Expected: set.is_empty() is true
   - Expected: set.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var set = HashSet.new()
set.insert("a")
set.insert("b")
set.insert("c")

set.clear()
expect(set.is_empty()).to_equal(true)
expect(set.len()).to_equal(0)
```

</details>

#### converts to vector

1. var set = HashSet new
2. set insert
3. set insert
4. set insert
   - Expected: items.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var set = HashSet.new()
set.insert("x")
set.insert("y")
set.insert("z")

val items = set.to_vec()
expect(items.len()).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
