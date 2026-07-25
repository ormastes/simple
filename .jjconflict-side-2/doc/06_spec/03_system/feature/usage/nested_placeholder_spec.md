# Nested Placeholder Scoping

> Tests that placeholder lambdas in nested call arguments maintain independent scoping at each nesting level. Verifies that inner and outer placeholders are independent, chained placeholders with nested any/all/filter work correctly, map with nested filter preserves scope, deeply nested chaining, string method placeholders, and edge cases like empty inner lists.

<!-- sdn-diagram:id=nested_placeholder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nested_placeholder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nested_placeholder_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nested_placeholder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nested Placeholder Scoping

Tests that placeholder lambdas in nested call arguments maintain independent scoping at each nesting level. Verifies that inner and outer placeholders are independent, chained placeholders with nested any/all/filter work correctly, map with nested filter preserves scope, deeply nested chaining, string method placeholders, and edge cases like empty inner lists.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/03_system/feature/usage/nested_placeholder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that placeholder lambdas in nested call arguments maintain independent scoping at
each nesting level. Verifies that inner and outer placeholders are independent, chained
placeholders with nested any/all/filter work correctly, map with nested filter preserves
scope, deeply nested chaining, string method placeholders, and edge cases like empty
inner lists.

## Scenarios

### Nested Placeholder Scoping

#### method call with nested placeholder

#### scopes inner and outer placeholders independently

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
val result = data.filter(_.any(_ > 5))
expect result == [[4, 5, 6], [7, 8, 9]]
```

</details>

#### filters arrays that have all elements above threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
val result = data.filter(_.all(_ > 3))
expect result == [[4, 5, 6], [7, 8, 9]]
```

</details>

#### chained placeholders with nested

#### chains outer filter with inner any

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[1, 5], [2, 3], [4, 6]]
val result = data.filter(_.any(_ > 4))
expect result == [[1, 5], [4, 6]]
```

</details>

#### map with nested filter

#### maps then filters within nested context

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[1, 2, 3, 4], [5, 6, 7, 8]]
val result = data.map(_.filter(_ > 2))
expect result == [[3, 4], [5, 6, 7, 8]]
```

</details>

#### simple nested independence

#### outer placeholder is independent of inner

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
# filter + map as separate operations (each has own _ scope)
val evens = nums.filter(_ % 2 == 0)
val doubled = evens.map(_ * 2)
expect doubled == [4, 8]
```

</details>

#### chained operations maintain separate scopes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val result = data.filter(_ > 1).map(_ * 3)
expect result == [6, 9, 12, 15]
```

</details>

#### deeply nested

#### handles three levels of nesting via chaining

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
val result = data.filter(_ > 3).filter(_ < 8).map(_ * 2)
expect result == [8, 10, 12, 14]
```

</details>

#### nested with string methods

#### filters strings containing substrings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val words = ["hello", "world", "help", "word"]
val result = words.filter(_.len() > 4)
expect result == ["hello", "world"]
```

</details>

#### edge cases

#### nested placeholder on empty inner list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[], [1, 2], []]
val result = data.filter(_.any(_ > 0))
expect result == [[1, 2]]
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
