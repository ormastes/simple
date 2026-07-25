# Method Reference Syntax

> Tests the `&:method` syntax which creates a lambda that calls the given method on its argument (inspired by Ruby's Symbol#to_proc). Covers basic method references with map and filter, chaining, storing references as values, usage with various types (strings, arrays), and combining method references with placeholder lambdas.

<!-- sdn-diagram:id=method_reference_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=method_reference_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

method_reference_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=method_reference_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Method Reference Syntax

Tests the `&:method` syntax which creates a lambda that calls the given method on its argument (inspired by Ruby's Symbol#to_proc). Covers basic method references with map and filter, chaining, storing references as values, usage with various types (strings, arrays), and combining method references with placeholder lambdas.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/03_system/feature/usage/method_reference_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the `&:method` syntax which creates a lambda that calls the given method on its
argument (inspired by Ruby's Symbol#to_proc). Covers basic method references with map
and filter, chaining, storing references as values, usage with various types (strings,
arrays), and combining method references with placeholder lambdas.

## Scenarios

### Method Reference

#### basic method reference

#### calls len on strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val words = ["hi", "hello", "hey"]
val result = words.map(&:len)
expect(result).to_equal([2, 5, 3])
```

</details>

#### with filter

#### filters with boolean method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[], [1], [], [2, 3]]
val result = data.filter(&:is_empty)
expect(result).to_equal([[], []])
```

</details>

#### chaining method references

#### chains map with method reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val words = ["hello", "world"]
val lengths = words.map(&:len)
expect(lengths).to_equal([5, 5])
```

</details>

#### method reference as value

#### stores len reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val get_len = &:len
expect(get_len("hello")).to_equal(5)
```

</details>

#### method reference with various types

#### calls len on arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[1, 2], [3], [4, 5, 6]]
val result = data.map(&:len)
expect(result).to_equal([2, 1, 3])
```

</details>

#### edge cases

#### method reference on empty collection

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [text] = []
val result = data.map(&:len)
expect(result).to_equal([])
```

</details>

#### method reference on single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = ["hello"]
val result = data.map(&:len)
expect(result).to_equal([5])
```

</details>

#### combines method reference with placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val words = ["hello", "hi", "hey", "howdy"]
val lengths = words.map(&:len)
val result = lengths.filter(_ > 3)
expect(result).to_equal([5, 5])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
