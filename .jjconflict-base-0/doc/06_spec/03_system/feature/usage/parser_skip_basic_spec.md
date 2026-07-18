# Skip Keyword - Basic Functionality

> Tests basic parsing and runtime behavior of the `skip` keyword as a standalone statement. Verifies that skip can be used in various contexts (if blocks, function bodies, loops), that it does not prevent subsequent code execution, does not affect return values, and does not alter variable scope.

<!-- sdn-diagram:id=parser_skip_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_skip_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_skip_basic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_skip_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skip Keyword - Basic Functionality

Tests basic parsing and runtime behavior of the `skip` keyword as a standalone statement. Verifies that skip can be used in various contexts (if blocks, function bodies, loops), that it does not prevent subsequent code execution, does not affect return values, and does not alter variable scope.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-002 |
| Category | Syntax |
| Status | Active |
| Source | `test/03_system/feature/usage/parser_skip_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests basic parsing and runtime behavior of the `skip` keyword as a standalone
statement. Verifies that skip can be used in various contexts (if blocks,
function bodies, loops), that it does not prevent subsequent code execution,
does not affect return values, and does not alter variable scope.

## Syntax

```simple
skip
fn test_function():
skip
return "completed"
```

## Scenarios

### Skip keyword - basic functionality

#### parses skip as standalone statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = true
skip
expect executed == true
```

</details>

#### parses skip with pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
pass
expect true
```

</details>

#### parses skip in if block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val condition = true
if condition:
    skip
expect true
```

</details>

#### parses skip in function body

1. fn test function
2. expect test function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_function():
    skip
    return "completed"
expect test_function() == "completed"
```

</details>

#### parses multiple skip statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
skip
skip
expect true
```

</details>

#### parses skip before expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
val result = 2 + 2
expect result == 4
```

</details>

<details>
<summary>Advanced: parses skip in loop</summary>

#### parses skip in loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..3:
    skip
    count = count + 1
expect count == 3
```

</details>


</details>

#### skip does not prevent execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = false
skip
executed = true
expect executed == true
```

</details>

#### skip does not affect return value

1. fn returns with skip
2. expect returns with skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn returns_with_skip():
    skip
    return "value"
expect returns_with_skip() == "value"
```

</details>

#### skip does not affect variable scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
val scoped = 100
expect scoped == 100
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
