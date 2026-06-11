# Short Grammar Interpreter Specification

> <details>

<!-- sdn-diagram:id=short_grammar_interpreter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=short_grammar_interpreter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

short_grammar_interpreter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=short_grammar_interpreter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Short Grammar Interpreter Specification

## Scenarios

### Short grammar interpreter

#### combines placeholder lambda with map

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [1, 2, 3].map(_ * 3)
expect(result).to_equal([3, 6, 9])
```

</details>

#### combines numbered placeholder with filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [1, 2, 3, 4, 5].filter(_1 > 2)
expect(result).to_equal([3, 4, 5])
```

</details>

#### keeps placeholder lambdas around nested calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ["2", "5"].map(int(_1))
expect(result).to_equal([2, 5])
```

</details>

#### keeps numbered placeholders inside string interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ["a", "b"].map("item:{_1}")
expect(result).to_equal(["item:a", "item:b"])
```

</details>

#### keeps numbered placeholders inside indexed string interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [[1, 2], [3, 4]].map("first:{_1[0]}")
expect(result).to_equal(["first:1", "first:3"])
```

</details>

#### keeps numbered placeholders inside formatted string interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [7].map("count:{_1:05d}")
expect(result).to_equal(["count:00007"])
```

</details>

#### uses numbered placeholders in string interpolation callback arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sg_apply_text_items(["World"], "Hello, {_1[0]}!")
expect(result).to_equal("Hello, World!")
```

</details>

#### uses method calls inside interpolated placeholder callbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sg_apply_text_items(["a", "b"], "got {_1.len()} items")
expect(result).to_equal("got 2 items")
```

</details>

#### uses tuple fields inside interpolated placeholder callbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(["i64", "bool"].enumerate().map("{_1.0}:{_1.1}") == ["0:i64", "1:bool"]).to_equal(true)
```

</details>

#### keeps placeholder lambdas around multi-argument calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [1, 2, 3].map(sg_len_plus("abcd", _1))
expect(result).to_equal([5, 6, 7])
```

</details>

#### combines method reference with placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lengths = ["a", "abcd", "xy"].map(&:len)
val result = lengths.filter(_ > 1)
expect(result).to_equal([4, 2])
```

</details>

#### uses placeholder field predicates

1. SgRow
2. SgRow
   - Expected: result.len() equals `1`
   - Expected: result[0].name equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    SgRow(name: "old", count: 1),
    SgRow(name: "new", count: 3)
]
val result = rows.filter(_1.name == "new" and _1.count > 2)
expect(result.len()).to_equal(1)
expect(result[0].name).to_equal("new")
```

</details>

#### uses placeholders inside inline if expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [1, 2, 3, 4].map(if _1 % 2 == 0: _1 * 10 else: 0)
expect(result).to_equal([0, 20, 0, 40])
```

</details>

#### uses inline if placeholder expressions as function arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sg_apply(4, if _1 % 2 == 0: _1 * 10 else: 0)
expect(result).to_equal(40)
```

</details>

#### uses inline if placeholder expressions that return nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sg_apply_optional(4, if _1 % 2 == 0: _1 * 10 else: nil)
expect(result).to_equal(40)
```

</details>

#### pipes through composed function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val transform = sg_double >> sg_add1
expect(4 |> transform).to_equal(9)
```

</details>

#### pipes comprehension result into lambda

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [for x in 0..4 if x % 2 == 0: x * x] |> &:len
expect(result).to_equal(2)
```

</details>

#### uses nil coalescing after option value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe: Option<i64> = nil
expect(maybe ?? 17).to_equal(17)
```

</details>

#### uses match expression as placeholder scrutinee in map

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [1, 2, 3].map(match _1:
    case 1: 10
    case 2: 20
    case _: 30
)
expect(result).to_equal([10, 20, 30])
```

</details>

#### uses match expression as placeholder scrutinee with wildcard default

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [4, 1, 2].map(match _1:
    case 1: "one"
    case _: "other"
)
expect(result).to_equal(["other", "one", "other"])
```

</details>

#### keeps explicit lambda readable for multiple arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sg_len_plus("abcd", 3)
expect(result).to_equal(7)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/parser/short_grammar_interpreter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Short grammar interpreter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
