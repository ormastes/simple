# Fluent Interface Specification

> <details>

<!-- sdn-diagram:id=fluent_interface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fluent_interface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fluent_interface_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fluent_interface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fluent Interface Specification

## Scenarios

### Fluent Interface Support

#### concatenates arrays with ->

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test functional update operator with array concatenation
var arr = [1, 2]
arr = arr + [3, 4]
expect(arr.len()).to_equal(4)
expect(arr[2]).to_equal(3)
```

</details>

#### maps array elements with ->

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test mapping over array elements
val arr = [1, 2, 3]
val doubled = arr.map(_ * 2)
expect(doubled[0]).to_equal(2)
expect(doubled[1]).to_equal(4)
expect(doubled[2]).to_equal(6)
```

</details>

#### filters array elements with ->

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test filtering array elements
val arr = [1, 2, 3, 4, 5]
val evens = arr.filter(_ % 2 == 0)
expect(evens.len()).to_equal(2)
expect(evens[0]).to_equal(2)
expect(evens[1]).to_equal(4)
```

</details>

#### chains multiple operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test chaining map and filter
val arr = [1, 2, 3, 4, 5]
val filtered = arr.filter(_ > 2)
val result = filtered.map(_ * 2)
expect(result.len()).to_equal(3)
expect(result[0]).to_equal(6)
expect(result[1]).to_equal(8)
expect(result[2]).to_equal(10)
```

</details>

#### works with method calls

1. list append
   - Expected: list.len() equals `3`
   - Expected: list[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test fluent interface with method chaining
var list = [1, 2]
list.append(3)
expect(list.len()).to_equal(3)
expect(list[2]).to_equal(3)
```

</details>

#### preserves array identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that operations preserve type
val arr = [1, 2, 3]
val same = arr.map(_1)
expect(same.len()).to_equal(3)
expect(same[0]).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/fluent_interface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Fluent Interface Support

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
