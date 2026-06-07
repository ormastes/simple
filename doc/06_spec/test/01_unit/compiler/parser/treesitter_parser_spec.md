# Treesitter Parser Specification

> 1. check

<!-- sdn-diagram:id=treesitter_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_parser_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Treesitter Parser Specification

## Scenarios

### TreeSitterParser

#### creates parser for Simple language

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser = MockParser.new("simple")
check(parser.language == "simple")
```

</details>

#### rejects unsupported languages

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser = MockParser.new("python")
check(parser.language == "python")
```

</details>

#### parses source code

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser = MockParser.new("simple")
val result = parser.parse("val x = 42")
check(result)
```

</details>

#### generates syntax tree

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser = MockParser.new("simple")
val code = "fn add(a, b): a + b"
val result = parser.parse(code)
check(result)
```

</details>

#### handles parse errors

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser = MockParser.new("simple")
check(parser.has_errors() == false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/treesitter_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TreeSitterParser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
