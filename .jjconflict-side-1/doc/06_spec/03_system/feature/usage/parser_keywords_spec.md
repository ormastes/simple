# Parser Keywords Specification

> Tests that all Simple language keywords are correctly recognized and

<!-- sdn-diagram:id=parser_keywords_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_keywords_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_keywords_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_keywords_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Keywords Specification

Tests that all Simple language keywords are correctly recognized and

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-KW-001 to #PARSER-KW-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/parser_keywords_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests that all Simple language keywords are correctly recognized and
parsed in their appropriate contexts.

## Scenarios

### Variable Keyword Parsing

#### val declares immutable variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect x == 42
```

</details>

#### var declares mutable variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 0
x = 42
expect x == 42
```

</details>

### Control Flow Keyword Parsing

#### parses if statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if true:
    1
else:
    0
expect result == 1
```

</details>

#### parses elif statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2
val result = if x == 1:
    "one"
elif x == 2:
    "two"
else:
    "other"
expect result == "two"
```

</details>

<details>
<summary>Advanced: parses while loop</summary>

#### parses while loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 0
while x < 3:
    x = x + 1
expect x == 3
```

</details>


</details>

<details>
<summary>Advanced: parses for loop</summary>

#### parses for loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in [1, 2, 3]:
    sum = sum + i
expect sum == 6
```

</details>


</details>

<details>
<summary>Advanced: parses break in loop</summary>

#### parses break in loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 0
while true:
    x = x + 1
    if x >= 5:
        break
expect x == 5
```

</details>


</details>

<details>
<summary>Advanced: parses continue in loop</summary>

#### parses continue in loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in [1, 2, 3, 4, 5]:
    if i == 3:
        continue
    sum = sum + i
expect sum == 12
```

</details>


</details>

#### parses return statement

1. fn early return
2. expect early return
3. expect early return


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn early_return(x: i64) -> i64:
    if x < 0:
        return 0
    x
expect early_return(-1) == 0
expect early_return(5) == 5
```

</details>

#### parses match expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match 42:
    case 0 => "zero"
    case 42 => "forty-two"
    case _ => "other"
expect result == "forty-two"
```

</details>

### Logic Keyword Parsing

#### parses and operator

1. expect
2. expect
3. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (true and true) == true
expect (true and false) == false
expect (false and true) == false
```

</details>

#### parses or operator

1. expect
2. expect
3. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (true or true) == true
expect (true or false) == true
expect (false or false) == false
```

</details>

#### parses not operator

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (not false) == true
expect (not true) == false
```

</details>

#### parses in operator

1. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 in [1, 2, 3]
expect not (5 in [1, 2, 3])
```

</details>

### Special Keyword Parsing

#### parses true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = true
expect x
```

</details>

#### parses false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = false
expect not x
```

</details>

#### parses nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
expect x == nil
```

</details>

#### parses self in method

1. expect p get x
2. expect p get y


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = TestPoint(x: 42, y: 10)
expect p.get_x() == 42
expect p.get_y() == 10
```

</details>

### Function Keyword Parsing

#### parses fn declaration

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64) -> i64:
    a + b
expect add(3, 4) == 7
```

</details>

#### parses nested function

1. fn outer
2. fn inner
3. inner
4. expect outer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn outer(x: i64) -> i64:
    fn inner(y: i64) -> i64:
        y * 2
    inner(x) + 1
expect outer(5) == 11
```

</details>

#### parses lambda expression

1. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val double = \x: x * 2
expect double(5) == 10
```

</details>

#### parses higher-order function

1. fn apply
2. f
3. expect apply


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(f: fn(i64) -> i64, x: i64) -> i64:
    f(x)
expect apply(\n: n + 1, 5) == 6
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
