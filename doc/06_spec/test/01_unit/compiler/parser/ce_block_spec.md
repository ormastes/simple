# Ce Block Specification

> <details>

<!-- sdn-diagram:id=ce_block_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ce_block_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ce_block_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ce_block_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ce Block Specification

## Scenarios

### ce block syntax - basic concepts

#### ce block equivalent with single bind evaluates

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Equivalent of: ce result_ce: bind x = 42; x
val x = 42
expect(x).to_equal(42)
```

</details>

#### ce block equivalent returns last expression value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Equivalent of: ce option_ce: bind a = 10; bind b = 20; a + b
val a = 10
val b = 20
val result = a + b
expect(result).to_equal(30)
```

</details>

#### ce block equivalent with text bind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "hello"
val result = name
expect(result).to_equal("hello")
```

</details>

### ce block syntax - bind statement

#### bind x = expr makes x available in rest of block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = 5
val second = first * 2
expect(second).to_equal(10)
```

</details>

#### multiple bind statements chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
val b = 2
val c = 3
val result = a + b + c
expect(result).to_equal(6)
```

</details>

#### bind name is accessible after bind statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = "world"
val result = "hello " + item
expect(result).to_equal("hello world")
```

</details>

### ce block syntax - builder names

#### result_ce builder concept

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 99
expect(x).to_equal(99)
```

</details>

#### option_ce builder concept

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 7
val result = x * 3
expect(result).to_equal(21)
```

</details>

#### custom_ce builder concept

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 100
expect(x).to_equal(100)
```

</details>

### ce block syntax - final expression

#### final expression is the return value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 100
expect(result).to_equal(100)
```

</details>

#### final expression after binds is the return value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5
val b = 10
val result = a * b
expect(result).to_equal(50)
```

</details>

#### final text expression after bind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "pre"
val suffix = "suf"
val result = prefix + "_" + suffix
expect(result).to_equal("pre_suf")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/ce_block_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ce block syntax - basic concepts
- ce block syntax - bind statement
- ce block syntax - builder names
- ce block syntax - final expression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
