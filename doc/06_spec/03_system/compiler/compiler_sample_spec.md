# compiler_sample_spec

> Simple Compiler Tests

<!-- sdn-diagram:id=compiler_sample_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_sample_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_sample_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_sample_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# compiler_sample_spec

Simple Compiler Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/compiler_sample_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Simple Compiler Tests
Feature: Simple language compilation
Category: Compiler System Tests
Status: Complete

Tests for Simple compiler basic operations including arithmetic, variables, control flow, and collections.

## Scenarios

### Simple Compiler

#### basic arithmetic

#### produces correct output for arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 + 3
expect(result).to(eq(5))
```

</details>

#### handles variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = 20
val sum = x + y
expect(sum).to(eq(30))
```

</details>

#### control flow

#### handles basic control flow

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val result = "smaller"
if x > 5:
    result = "greater"
expect(result).to(eq("greater"))
```

</details>

#### collections

#### handles arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
expect(arr.len()).to(eq(3))
expect(arr[0]).to(eq(1))
```

</details>

#### handles dicts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"name": "Alice", "age": 30}
expect(d["name"]).to(eq("Alice"))
expect(d["age"]).to(eq(30))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
