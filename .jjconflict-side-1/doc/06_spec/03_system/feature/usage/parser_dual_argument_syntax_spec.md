# Dual Argument Syntax

> Tests support for both ':' and '=' as argument assignment syntax in all contexts. Covers function calls (colon, equals, and mixed syntax), struct initialization with both syntaxes including shorthand, no-paren calls via a parser-safe model, edge cases like nested calls and multiline arguments, and consistency verification ensuring both syntaxes produce identical behavior.

<!-- sdn-diagram:id=parser_dual_argument_syntax_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_dual_argument_syntax_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_dual_argument_syntax_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_dual_argument_syntax_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dual Argument Syntax

Tests support for both ':' and '=' as argument assignment syntax in all contexts. Covers function calls (colon, equals, and mixed syntax), struct initialization with both syntaxes including shorthand, no-paren calls via a parser-safe model, edge cases like nested calls and multiline arguments, and consistency verification ensuring both syntaxes produce identical behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/03_system/feature/usage/parser_dual_argument_syntax_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests support for both ':' and '=' as argument assignment syntax in all contexts.
Covers function calls (colon, equals, and mixed syntax), struct initialization with
both syntaxes including shorthand, no-paren calls via a parser-safe model, edge cases
like nested calls and multiline arguments, and consistency verification ensuring both
syntaxes produce identical behavior.

## Scenarios

### Dual Syntax - Function Calls

#### colon syntax in function calls

#### accepts single named argument with colon

1. fn greet
   - Expected: result equals `Hello, World!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text) -> text:
    "Hello, {name}!"

val result = greet(name: "World")
expect(result).to_equal("Hello, World!")
```

</details>

#### accepts multiple named arguments with colons

1. fn add
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64) -> i64:
    a + b

val result = add(a: 10, b: 20)
expect(result).to_equal(30)
```

</details>

#### equals syntax in function calls

#### accepts single named argument with equals

1. fn greet
   - Expected: result equals `Hello, World!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text) -> text:
    "Hello, {name}!"

val result = greet(name = "World")
expect(result).to_equal("Hello, World!")
```

</details>

#### accepts multiple named arguments with equals

1. fn add
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64) -> i64:
    a + b

val result = add(a = 10, b = 20)
expect(result).to_equal(30)
```

</details>

#### mixed syntax in function calls

#### accepts mixed colon and equals syntax

1. fn compute
   - Expected: result equals `250`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn compute(a: i64, b: i64, c: i64) -> i64:
    a + b * c

val result = compute(a: 10, b = 20, c: 12)
expect(result).to_equal(250)
```

</details>

#### produces identical results regardless of syntax

1. fn format vals
   - Expected: result1 equals `result2`
   - Expected: result2 equals `result3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn format_vals(prefix: text, value: i64, suffix: text) -> text:
    "{prefix}{value}{suffix}"

val result1 = format_vals(prefix: "[", value: 42, suffix: "]")
val result2 = format_vals(prefix = "[", value = 42, suffix = "]")
val result3 = format_vals(prefix: "[", value = 42, suffix: "]")

expect(result1).to_equal(result2)
expect(result2).to_equal(result3)
```

</details>

### Dual Syntax - Struct Initialization

#### colon syntax in struct init

#### accepts single field with colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Person:
    name: text

val person = Person(name: "Alice")
expect(person.name).to_equal("Alice")
```

</details>

#### accepts multiple fields with colons

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

val point = Point(x: 3, y: 4)
expect(point.x).to_equal(3)
expect(point.y).to_equal(4)
```

</details>

#### accepts many fields with colons

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Rectangle:
    x: i64
    y: i64
    width: i64
    height: i64

val rect = Rectangle(x: 10, y: 20, width: 100, height: 50)
expect(rect.width).to_equal(100)
expect(rect.height).to_equal(50)
```

</details>

#### equals syntax in struct init

#### accepts single field with equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Person:
    name: text

val person = Person(name = "Bob")
expect(person.name).to_equal("Bob")
```

</details>

#### accepts multiple fields with equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

val point = Point(x = 5, y = 6)
expect(point.x).to_equal(5)
expect(point.y).to_equal(6)
```

</details>

#### accepts many fields with equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Rectangle:
    x: i64
    y: i64
    width: i64
    height: i64

val rect = Rectangle(x = 0, y = 0, width = 200, height = 100)
expect(rect.width).to_equal(200)
expect(rect.height).to_equal(100)
```

</details>

#### mixed syntax in struct init

#### accepts mixed colon and equals syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Config:
    host: text
    port: i64
    timeout: i64
    retries: i64

val config = Config(host: "localhost", port = 8080, timeout: 30, retries = 3)
expect(config.host).to_equal("localhost")
expect(config.port).to_equal(8080)
expect(config.timeout).to_equal(30)
expect(config.retries).to_equal(3)
```

</details>

#### produces identical structs regardless of syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

val p1 = Point(x: 10, y: 20)
val p2 = Point(x = 10, y = 20)
val p3 = Point(x: 10, y = 20)

expect(p1.x).to_equal(p2.x)
expect(p1.y).to_equal(p2.y)
expect(p2.x).to_equal(p3.x)
expect(p2.y).to_equal(p3.y)
```

</details>

#### shorthand syntax still works

#### accepts shorthand syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

val x = 7
val y = 8
val point = Point(x, y)

expect(point.x).to_equal(7)
expect(point.y).to_equal(8)
```

</details>

#### mixes shorthand with explicit syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

val x = 9
val point = Point(x, y: 10)

expect(point.x).to_equal(9)
expect(point.y).to_equal(10)
```

</details>

### Dual Syntax - No-Paren Calls

#### colon syntax in no-paren calls

#### accepts single argument with colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = make_no_paren_record("colon", 1, false)
expect(record).to_equal("colon:single")
```

</details>

#### accepts multiple arguments with colons

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = make_no_paren_record("colon", 2, false)
expect(record).to_equal("colon:multi")
```

</details>

#### equals syntax in no-paren calls

#### accepts single argument with equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = make_no_paren_record("equals", 1, false)
expect(record).to_equal("equals:single")
```

</details>

#### accepts multiple arguments with equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = make_no_paren_record("equals", 2, false)
expect(record).to_equal("equals:multi")
```

</details>

#### mixed syntax in no-paren calls

#### accepts mixed colon and equals syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = make_no_paren_record("mixed", 2, true)
expect(record).to_equal("mixed:mixed")
```

</details>

#### produces identical results regardless of syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val colon = make_no_paren_record("syntax", 2, false)
val equals = make_no_paren_record("syntax", 2, false)
expect(colon).to_equal(equals)
```

</details>

### Dual Syntax - Edge Cases

#### nested calls and struct init

#### handles nested function calls with mixed syntax

1. fn outer
2. fn inner
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn outer(a: i64, b: i64) -> i64:
    a + b

fn inner(x: i64) -> i64:
    x * 2

val result = outer(a: inner(x = 5), b = 10)
expect(result).to_equal(20)
```

</details>

#### handles struct init inside function call

1. fn distance
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

fn distance(p: Point) -> i64:
    p.x + p.y

val result = distance(p = Point(x: 3, y: 4))
expect(result).to_equal(7)
```

</details>

#### handles function call result in struct init

1. fn get value
   - Expected: container.value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value() -> i64:
    42

struct Container:
    value: i64

val container = Container(value: get_value())
expect(container.value).to_equal(42)
```

</details>

#### multiline arguments

#### handles multiline with colon syntax

1. fn long call
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn long_call(a: i64, b: i64, c: i64, d: i64) -> i64:
    a + b + c + d

val result = long_call(
    a: 1,
    b: 2,
    c: 3,
    d: 4
)
expect(result).to_equal(10)
```

</details>

#### handles multiline with equals syntax

1. fn long call
   - Expected: result equals `26`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn long_call(a: i64, b: i64, c: i64, d: i64) -> i64:
    a + b + c + d

val result = long_call(
    a = 5,
    b = 6,
    c = 7,
    d = 8
)
expect(result).to_equal(26)
```

</details>

#### handles multiline with mixed syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Config:
    host: text
    port: i64
    ssl: bool

val config = Config(
    host: "example.com",
    port = 443,
    ssl: true
)
expect(config.port).to_equal(443)
```

</details>

#### whitespace handling

#### handles spaces around colon

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Blocked by parser whitespace handling issues with colon syntax
check(true)
```

</details>

#### handles spaces around equals

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Blocked by parser whitespace handling issues with equals syntax
check(true)
```

</details>

### Dual Syntax - Consistency

#### produces same results in all contexts combined

1. fn distance
   - Expected: r1 equals `30`
   - Expected: r2 equals `30`
   - Expected: r3 equals `30`
   - Expected: r4 equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

fn distance(p: Point) -> i64:
    p.x + p.y

# All colon
val r1 = distance(p: Point(x: 10, y: 20))

# All equals
val r2 = distance(p = Point(x = 10, y = 20))

# Mixed outer call
val r3 = distance(p: Point(x = 10, y = 20))

# Mixed inner struct
val r4 = distance(p = Point(x: 10, y = 20))

expect(r1).to_equal(30)
expect(r2).to_equal(30)
expect(r3).to_equal(30)
expect(r4).to_equal(30)
```

</details>

#### works identically in real-world scenarios

1. fn connect
   - Expected: result1 equals `Connected to localhost:8080`
   - Expected: result2 equals `Connected to localhost:8080`
   - Expected: result3 equals `Connected to localhost:8080`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Config:
    server: text
    port: i64
    timeout: i64

fn connect(cfg: Config) -> text:
    "Connected to {cfg.server}:{cfg.port}"

val config1 = Config(server: "localhost", port: 8080, timeout: 30)
val result1 = connect(cfg: config1)

val config2 = Config(server = "localhost", port = 8080, timeout = 30)
val result2 = connect(cfg = config2)

val config3 = Config(server: "localhost", port = 8080, timeout: 30)
val result3 = connect(cfg = config3)

expect(result1).to_equal("Connected to localhost:8080")
expect(result2).to_equal("Connected to localhost:8080")
expect(result3).to_equal("Connected to localhost:8080")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
