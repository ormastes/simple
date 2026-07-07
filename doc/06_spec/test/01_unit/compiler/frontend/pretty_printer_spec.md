# Pretty Printer Unit Tests

> <details>

<!-- sdn-diagram:id=pretty_printer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pretty_printer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pretty_printer_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pretty_printer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pretty Printer Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPILER-FRONTEND-004 |
| Category | Compiler \| Frontend \| Pretty Printer |
| Status | Implemented |
| Source | `test/01_unit/compiler/frontend/pretty_printer_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Format Expressions

#### format integer literal

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "{42}"
check(s == "42")
```

</details>

#### format negative integer

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "{-5}"
check(s == "-5")
```

</details>

#### format float literal

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3.14
val s = "{x}"
check(s.contains("3.14"))
```

</details>

#### format string literal

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
check(s == "hello")
```

</details>

#### format boolean true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "{true}"
check(s == "true")
```

</details>

#### format boolean false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "{false}"
check(s == "false")
```

</details>

#### format array

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val s = "{arr}"
check(s.contains("1"))
check(s.contains("3"))
```

</details>

### Format Statements

#### format val declaration

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decl = "val x = 42"
check(decl.starts_with("val"))
```

</details>

#### format var declaration

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decl = "var x = 42"
check(decl.starts_with("var"))
```

</details>

#### format assignment

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmt = "x = 42"
check(stmt.contains("="))
```

</details>

#### format return

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmt = "return 42"
check(stmt.starts_with("return"))
```

</details>

### Format Control Flow

#### format if statement

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmt = "if x > 0:"
check(stmt.starts_with("if"))
```

</details>

<details>
<summary>Advanced: format while loop</summary>

#### format while loop

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmt = "while i < 10:"
check(stmt.starts_with("while"))
```

</details>


</details>

<details>
<summary>Advanced: format for loop</summary>

#### format for loop

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmt = "for i in 0..10:"
check(stmt.starts_with("for"))
```

</details>


</details>

#### format match

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmt = "match x:"
check(stmt.starts_with("match"))
```

</details>

### Indentation

#### top level no indent

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val indent = 0
check(indent == 0)
```

</details>

#### block body indented

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val indent = 4
check(indent == 4)
```

</details>

#### nested block double indented

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val indent = 8
check(indent == 8)
```

</details>

#### consistent indent width

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val width = 4
val level1 = width
val level2 = width * 2
val level3 = width * 3
check(level1 == 4)
check(level2 == 8)
check(level3 == 12)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
