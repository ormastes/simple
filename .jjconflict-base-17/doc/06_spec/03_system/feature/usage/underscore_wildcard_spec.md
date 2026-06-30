# Underscore Wildcard Specification

> Tests for underscore (_) as a wildcard placeholder in various contexts:

<!-- sdn-diagram:id=underscore_wildcard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=underscore_wildcard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

underscore_wildcard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=underscore_wildcard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Underscore Wildcard Specification

Tests for underscore (_) as a wildcard placeholder in various contexts:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/underscore_wildcard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for underscore (_) as a wildcard placeholder in various contexts:
- Lambda parameters: `\_: expr` to ignore arguments
- For loop patterns: `for _ in items:` to iterate without binding
- Match patterns: `case _:` as a catch-all wildcard

## Scenarios

### Underscore Wildcard Support

### in lambda parameters

#### ignores single argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = \_: 42
expect(f(100)).to_equal(42)
expect(f(0)).to_equal(42)
expect(f(-5)).to_equal(42)
```

</details>

#### works in map to transform values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3, 4, 5]
val result = items.map(\_: 0)
expect(result.len()).to_equal(5)
```

</details>

### in for loop patterns

#### iterates without binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 0
for _ in 0..5:
    total = total + 1
expect(total).to_equal(5)
```

</details>

#### uses sum_n_times helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sum_n_times(value=10, n=3)).to_equal(30)
expect(sum_n_times(value=5, n=4)).to_equal(20)
```

</details>

#### works with list iteration

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for _ in [1, 2, 3]:
    count = count + 1
expect(count).to_equal(3)
```

</details>

### in match patterns

#### catches unmatched cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(classify_number(0)).to_equal("zero")
expect(classify_number(1)).to_equal("one")
expect(classify_number(2)).to_equal("two")
expect(classify_number(100)).to_equal("many")
expect(classify_number(-1)).to_equal("many")
```

</details>

#### ignores enum payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_some(MyOption.Some(42))).to_equal(true)
expect(is_some(MyOption.Some(0))).to_equal(true)
expect(is_some(MyOption.Nil)).to_equal(false)
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
