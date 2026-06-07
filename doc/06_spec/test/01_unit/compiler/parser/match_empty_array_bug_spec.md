# Match Empty Array Bug Specification

> 1. fn get items workaround

<!-- sdn-diagram:id=match_empty_array_bug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=match_empty_array_bug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

match_empty_array_bug_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=match_empty_array_bug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Match Empty Array Bug Specification

## Scenarios

### Match Empty Array Bug

#### reproduces parser error with direct [] return

1. fn get items workaround
2. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This pattern causes parse error during module loading:
# fn get_items(value: TestEnum) -> [i64]:
#     match value:
#         case Empty: []        <- PARSE ERROR
#         case Single(x): [x]
#         case Multiple(x, y): [x, y]

# Workaround: Assign to variable first
fn get_items_workaround(value: TestEnum) -> [i64]:
    match value:
        case Empty:
            val empty: [i64] = []
            empty
        case Single(x):
            [x]
        case Multiple(x, y):
            [x, y]

val result = get_items_workaround(TestEnum.Empty)
expect result.len() == 0
```

</details>

#### works with non-empty array literal

1. fn get items
2. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_items(value: TestEnum) -> [i64]:
    match value:
        case Empty:
            [0]        # Non-empty works fine
        case Single(x):
            [x]
        case Multiple(x, y):
            [x, y]

val result = get_items(TestEnum.Empty)
expect result.len() == 1
```

</details>

#### works when assigning to variable first

1. fn get items
2. expect items len


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_items(value: TestEnum) -> [i64]:
    val result = match value:
        case Empty:
            val empty: [i64] = []
            empty
        case Single(x): [x]
        case Multiple(x, y): [x, y]
    result

val items = get_items(TestEnum.Empty)
expect items.len() == 0
```

</details>

### Related Patterns

#### direct nil return works

1. fn get optional


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_optional(flag: bool) -> i64?:
    match flag:
        case true: Some(42)
        case false: nil    # nil works fine

val result = get_optional(false)
expect not result.?
```

</details>

#### direct empty string works

1. fn get text
2. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_text(flag: bool) -> text:
    match flag:
        case true: "hello"
        case false: ""     # Empty string works fine

val result = get_text(false)
expect result.len() == 0
```

</details>

#### direct empty dict might fail

1. fn get dict
2. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This might also fail - needs testing
fn get_dict(flag: bool) -> Dict<text, i64>:
    match flag:
        case true: {"key": 42}
        case false:
            val empty: Dict<text, i64> = {}
            empty  # Using workaround

val result = get_dict(false)
expect result.len() == 0
```

</details>

### Bug Impact

#### affects function returning arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pattern used in loop_opt.spl:142-160
# fn get_successors(term: MirTerminator) -> [BlockId]:
#     match term:
#         case Return(_): []      <- BLOCKS MODULE LOADING
#         case Unreachable: []    <- BLOCKS MODULE LOADING
#         case _: []              <- BLOCKS MODULE LOADING

expect true  # Documenting the issue
```

</details>

#### workaround adds 2 extra lines per empty case

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Instead of:
#   case Empty: []
#
# Need:
#   case Empty:
#       val empty: [T] = []
#       empty

expect true  # Documenting workaround cost
```

</details>

### Expected Behavior

#### should allow direct [] return like other literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# These all work:
# case X: 42           # Direct integer literal
# case X: "text"       # Direct string literal
# case X: true         # Direct boolean literal
# case X: [1, 2, 3]    # Non-empty array literal
#
# This should also work:
# case X: []           # Empty array literal <- BUG

expect true  # Documenting expected behavior
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/match_empty_array_bug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Match Empty Array Bug
- Related Patterns
- Bug Impact
- Expected Behavior

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
