# Treesitter Query Specification

> 1. check

<!-- sdn-diagram:id=treesitter_query_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_query_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_query_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_query_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Treesitter Query Specification

## Scenarios

### Query Creation

#### creates query for Simple language

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = MockQuery.new("(identifier) @name")
check(query.pattern.len() > 0)
```

</details>

#### handles invalid query

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = MockQuery.new("invalid pattern")
check(query.pattern.len() > 0)
```

</details>

### Query Execution

#### matches patterns

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = MockQuery.new("(identifier)")
check(query.execute())
```

</details>

#### captures nodes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = MockQuery.new("(identifier) @var")
val captures = query.get_captures()
check(captures.len() > 0)
```

</details>

#### supports predicates

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = MockQuery.new("(function_definition) @func")
check(query.execute())
```

</details>

### QueryCursor

#### iterates matches

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cursor = MockQueryCursor.new()
check(cursor.next_match())
```

</details>

#### supports byte range

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cursor = MockQueryCursor.new()
check(cursor.supports_byte_range())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/treesitter_query_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Query Creation
- Query Execution
- QueryCursor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
