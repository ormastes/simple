# Basic Expressions (Python-Inspired Sample)

> Tests compilation of basic expression patterns inspired by Python syntax including arithmetic, string operations, and comparisons. Verifies that Python-like expression idioms compile correctly through the native compilation pipeline.

<!-- sdn-diagram:id=basic_expressions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=basic_expressions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

basic_expressions_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=basic_expressions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basic Expressions (Python-Inspired Sample)

Tests compilation of basic expression patterns inspired by Python syntax including arithmetic, string operations, and comparisons. Verifies that Python-like expression idioms compile correctly through the native compilation pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/sample/python_inspired_sample/basic_expressions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compilation of basic expression patterns inspired by Python syntax including
arithmetic, string operations, and comparisons. Verifies that Python-like expression
idioms compile correctly through the native compilation pipeline.

## Scenarios

### Basic Expressions

#### arithmetic expressions

#### evaluates addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 + 3 == 5
```

</details>

#### evaluates subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 - 4 == 6
```

</details>

#### evaluates multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 3 * 4 == 12
```

</details>

#### evaluates division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 / 2 == 5
```

</details>

#### evaluates modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 % 3 == 1
```

</details>

#### comparison operators

#### compares with less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 3 < 5
```

</details>

#### compares with greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 7 > 4
```

</details>

#### compares equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 == 5
```

</details>

#### compares inequality

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 3 != 4
```

</details>

#### boolean expressions

#### evaluates logical and

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true && true == true
expect true && false == false
```

</details>

#### evaluates logical or

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect false || true == true
expect false || false == false
```

</details>

#### evaluates logical not

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not false == true
expect not true == false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
