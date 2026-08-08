# Match Expression Separator Specification

> The runtime has two match parsers:

<!-- sdn-diagram:id=parser_match_expression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_match_expression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_match_expression_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_match_expression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Match Expression Separator Specification

The runtime has two match parsers:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-ME-001 to #PARSER-ME-010 |
| Category | Infrastructure \| Parser |
| Status | In Progress |
| Source | `test/03_system/feature/usage/parser_match_expression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Bug: Match arm separators in expression context

The runtime has two match parsers:
1. Statement-level: `case` keyword + `:` (works, but no return value)
2. Expression-level: only `=>` works (returns value, rejects `:` and `case`)

The expression-level parser should also accept `:` and `case` keyword.
Fix: src/app/parser/expr/control.spl lines 78-94

Broken syntax (expression context):
val y = match x:
42: "found"           # error: expected FatArrow, found Colon
val y = match x:
case 42: "found"     # error: expected pattern, found Case

After rebuild, uncomment skipped tests in Group 3 below.

## Scenarios

### Match Statement case+colon

#### executes matching arm for integer patterns

1. expect match side effect
2. expect match side effect
3. expect match side effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_side_effect(0) == "zero"
expect match_side_effect(1) == "one"
expect match_side_effect(99) == "other"
```

</details>

#### executes arm with guard clauses

1. expect match guard side effect
2. expect match guard side effect
3. expect match guard side effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_guard_side_effect(-5) == "negative"
expect match_guard_side_effect(0) == "zero"
expect match_guard_side_effect(42) == "positive"
```

</details>

### Match Expression FatArrow

#### single-expression arms return values

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v1 = match 42:
    42 => "found"
    _ => "other"
expect v1 == "found"
val v2 = match 99:
    42 => "found"
    _ => "other"
expect v2 == "other"
```

</details>

#### multi-line arm bodies return last expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = match 42:
    42 =>
        val x = 42 + 1
        x
    _ =>
        0
expect output == 43
```

</details>

#### multiple statements in arm body

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = match 10:
    10 =>
        val a = 10 * 2
        val b = a + 5
        b
    _ =>
        -1
expect output == 25
```

</details>

#### guard clauses select correct arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = match 42:
    x if x > 100 => "big"
    x if x > 0 => "positive"
    _ => "other"
expect output == "positive"
```

</details>

#### nested match expressions return values

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
val output = match a:
    1 =>
        val inner = match 2:
            2 => "one-two"
            _ => "one-other"
        inner
    _ =>
        "other"
expect output == "one-two"
```

</details>

### Match Statement-Expression Consistency

#### expression and statement match get same answers

1. expect match side effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr_val = match 42:
    42 => "found_expr"
    _ => "other_expr"
expect expr_val == "found_expr"
expect match_side_effect(0) == "zero"
```

</details>

#### expression match multi-line returns correct value

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = match 2:
    1 =>
        100
    2 =>
        200
    _ =>
        0
expect output == 200
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
