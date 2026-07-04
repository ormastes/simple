# parser_improvements_spec

> Parser Improvement Tests for the Simple language compiler.

<!-- sdn-diagram:id=parser_improvements_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_improvements_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_improvements_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_improvements_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# parser_improvements_spec

Parser Improvement Tests for the Simple language compiler.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/parser_improvements_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Parser Improvement Tests for the Simple language compiler.
Validates implemented parser enhancements including match arrow syntax,
function return types, generics, struct literals, and string operations.

## Scenarios

### Parser Improvements - Working Features

#### Match Arrow Syntax

#### supports arrow syntax in match expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 2
val result = match value:
    1 -> "one"
    2 -> "two"
    _ -> "other"
expect result == "two"
```

</details>

#### supports multiple patterns with arrows

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3
val msg = match x:
    0 -> "zero"
    1 -> "one"
    2 -> "two"
    _ -> "many"
expect msg == "many"
```

</details>

#### Function Return Types

#### parses return type annotations

1. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect double(5) == 10
```

</details>

#### supports complex return types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_pair(42)
expect result.is_some == true
```

</details>

#### Generic Types

#### supports Option generic type

1. expect v unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = make_pair(42)
expect v.unwrap() == 42
```

</details>

#### supports Result generic type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = compute()
expect r.is_ok == true
```

</details>

#### Struct Literal Syntax

#### supports named field initialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point { x: 10, y: 20 }
expect p.x == 10
expect p.y == 20
```

</details>

#### supports multi-line struct literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Config {
    name: "test",
    value: 42
}
expect c.name == "test"
```

</details>

#### text Multiplication

#### repeats string with * operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sep = "=" * 5
expect sep == "====="
```

</details>

#### handles zero repetition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = "x" * 0
expect empty == ""
```

</details>

#### handles single repetition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val single = "ab" * 1
expect single == "ab"
```

</details>

### Parser Improvements - Now Implemented

#### Multi-line Method Chaining

#### supports method chaining across lines

1. static fn start
2. ChainBuilder
3. me add
4.  add
5.  add


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multi-line chaining now works
class ChainBuilder:
    val_: i32
    static fn start() -> ChainBuilder:
        ChainBuilder(val_: 0)
    me add(n: i32) -> ChainBuilder:
        self.val_ = self.val_ + n
        self
val result = ChainBuilder__start()
    .add(1)
    .add(2)
expect result.val_ == 3
```

</details>

#### supports fluent interface pattern

1. static fn create
2. Fluent
3. me append
4.  append
5.  append


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Fluent:
    data: text
    static fn create() -> Fluent:
        Fluent(data: "")
    me append(s: text) -> Fluent:
        self.data = self.data + s
        self
val f = Fluent__create()
    .append("a")
    .append("b")
expect f.data == "ab"
```

</details>

#### Enum Variant Construction

#### supports qualified enum variant creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val variant = ParserImprovementVariant.Ready
val result = match variant:
    ParserImprovementVariant.Ready -> "ready"
    _ -> "other"
expect result == "ready"
```

</details>

#### supports enum variant with data

1. ParserImprovementVariant WithData


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val variant = ParserImprovementVariant.WithData(7)
val result = match variant:
    ParserImprovementVariant.WithData(value) -> value
    _ -> 0
expect result == 7
```

</details>

#### Qualified Method Calls

#### supports method call chains

1. static fn create
2. Container
3. fn get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Basic method chaining works
class Container:
    inner_val: i32
    static fn create() -> Container:
        Container(inner_val: 42)
    fn get_value() -> i32:
        self.inner_val
val v = Container__create().get_value()
expect v == 42
```

</details>

#### supports module-level access

1. sp expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Module function access works via alias
# sp imported at module level (use inside it blocks causes stack overflow)
sp.expect(true == true)
```

</details>

#### String Interpolation

#### supports string interpolation with variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "World"
val greeting = "Hello, {name}!"
expect greeting == "Hello, World!"
```

</details>

#### supports expressions in braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val y = 3
val result = "Sum: {x + y}"
expect result == "Sum: 8"
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
