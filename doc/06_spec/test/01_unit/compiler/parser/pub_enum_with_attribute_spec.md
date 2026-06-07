# Pub Enum With Attribute Specification

> <details>

<!-- sdn-diagram:id=pub_enum_with_attribute_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pub_enum_with_attribute_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pub_enum_with_attribute_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pub_enum_with_attribute_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pub Enum With Attribute Specification

## Scenarios

### pub enum with attribute

#### parses a known attribute followed by pub enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
"Simple unit-variant enum after an attribute must parse."
val c = Color.Red
expect(c).to_equal(Color.Red)
```

</details>

#### parses a known attribute followed by pub enum with data variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
"Data-variant enum after an attribute must parse."
val s = Shape.Circle(2.0)
expect(s).to_equal(Shape.Circle(2.0))
```

</details>

#### parses a known attribute followed by pub union

1. "Public union
   - Expected: t equals `Tagged.Int(42)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
"Public union (enum alias) after an attribute must parse."
val t = Tagged.Int(42)
expect(t).to_equal(Tagged.Int(42))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/pub_enum_with_attribute_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pub enum with attribute

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
