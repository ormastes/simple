# Parser Attribute Specification

> <details>

<!-- sdn-diagram:id=parser_attribute_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_attribute_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_attribute_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_attribute_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Attribute Specification

## Scenarios

### Parser - Attribute Syntax

#### parses @ attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @attr
# Traditional attribute syntax
expect(1).to_equal(1)
```

</details>

#### parses #[] attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @attr
# New attribute syntax
expect(1).to_equal(1)
```

</details>

#### parses @ attribute with arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @timeout(5000)
# Arguments should be parsed
expect(1).to_equal(1)
```

</details>

#### parses #[] attribute with arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @timeout(5000)
# Arguments should be parsed
expect(1).to_equal(1)
```

</details>

#### parses multiple @ attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @attr1
# @attr2
# Both should be captured
expect(1).to_equal(1)
```

</details>

#### parses multiple #[] attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @attr1
# @attr2
# Both should be captured
expect(1).to_equal(1)
```

</details>

#### parses mixed @ and #[] attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @repr(C)
# @packed
# Both should be captured
expect(1).to_equal(1)
```

</details>

### Parser - Attribute Application

#### applies attributes to functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @timeout(5000)
# fn test():
# Attribute should attach to function
expect(1).to_equal(1)
```

</details>

#### applies attributes to classes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @repr(C)
# class Data:
# Attribute should attach to class
expect(1).to_equal(1)
```

</details>

#### applies attributes to actors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @distributed
# actor Worker:
# Attribute should attach to actor
expect(1).to_equal(1)
```

</details>

#### applies attributes to structs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @packed
# struct Point:
# Attribute should attach to struct
expect(1).to_equal(1)
```

</details>

### Parser - Attribute Arguments

#### parses single argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @timeout(5000)
# Single numeric argument
expect(1).to_equal(1)
```

</details>

#### parses multiple arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @tag("slow", "integration")
# Multiple string arguments
expect(1).to_equal(1)
```

</details>

#### parses complex arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @config(key: "value", count: 42)
# Named arguments
expect(1).to_equal(1)
```

</details>

#### handles empty parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @attr()
# Empty argument list
expect(1).to_equal(1)
```

</details>

### Parser - Attribute Edge Cases

#### handles attribute before pub

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @test
# pub fn test():
# Attribute before visibility
expect(1).to_equal(1)
```

</details>

#### handles nested attribute arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @config([1, 2, 3])
# Nested brackets/parens
expect(1).to_equal(1)
```

</details>

#### preserves attribute order

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @first
# @second
# Order should be maintained
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/parser_attribute_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Parser - Attribute Syntax
- Parser - Attribute Application
- Parser - Attribute Arguments
- Parser - Attribute Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
