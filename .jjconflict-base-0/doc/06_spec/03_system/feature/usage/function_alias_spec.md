# Function Alias (Deprecated Delegation)

> Tests the deprecated `fn name = target` function alias syntax that the desugar pipeline transforms into explicit delegation. Validates basic alias calling, return value preservation for text and integer types, alias chaining (alias of alias), and that original functions remain callable alongside their aliases.

<!-- sdn-diagram:id=function_alias_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=function_alias_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

function_alias_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=function_alias_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Function Alias (Deprecated Delegation)

Tests the deprecated `fn name = target` function alias syntax that the desugar pipeline transforms into explicit delegation. Validates basic alias calling, return value preservation for text and integer types, alias chaining (alias of alias), and that original functions remain callable alongside their aliases.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FWD-001 |
| Category | Syntax |
| Status | Active |
| Source | `test/03_system/feature/usage/function_alias_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the deprecated `fn name = target` function alias syntax that the desugar
pipeline transforms into explicit delegation. Validates basic alias calling,
return value preservation for text and integer types, alias chaining (alias of
alias), and that original functions remain callable alongside their aliases.

## Syntax

```simple
fn sum(a: i64, b: i64) -> i64:
add(a, b)
val result = sum(3, 4)  # calls add(3, 4) via delegation
```
Function Alias Specification

Feature IDs: #FWD-001
Category: Syntax
Difficulty: 2/5
Status: DEPRECATED - use explicit delegation instead

The `fn name = target` syntax is deprecated. The desugar pipeline
transforms it into explicit delegation: `fn name(params): target(params)`.
This test verifies the delegation pattern works correctly.

Example (deprecated):  fn println = print
Preferred:             fn println(msg: text): print(msg)

## Scenarios

### function alias (deprecated delegation)

#### basic alias

#### calls target function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sum(3, 4)
expect(result).to_equal(7)
```

</details>

#### works with zero arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sum(0, 0)
expect(result).to_equal(0)
```

</details>

#### works with negative arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sum(-1, -2)
expect(result).to_equal(-3)
```

</details>

#### alias preserves behavior

#### preserves return value for text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = say_hello("World")
expect(msg).to_equal("Hello, World")
```

</details>

#### preserves return value for integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = same(42)
expect(result).to_equal(42)
```

</details>

#### alias chain

#### alias of alias works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = times_two(5)
expect(result).to_equal(10)
```

</details>

#### intermediate alias also works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = multiply_by_two(7)
expect(result).to_equal(14)
```

</details>

#### original function

#### original still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add(1, 2)
expect(result).to_equal(3)
```

</details>

#### alias and original return same result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = add(10, 20)
val r2 = sum(10, 20)
expect(r1).to_equal(r2)
```

</details>

#### void alias

#### void alias is callable

1. do nothing
   - Expected: noop_call_count equals `before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = noop_call_count
do_nothing()
expect(noop_call_count).to_equal(before + 1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
