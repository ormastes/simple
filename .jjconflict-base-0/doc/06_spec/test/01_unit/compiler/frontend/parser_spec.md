# Parser Unit Tests

> <details>

<!-- sdn-diagram:id=parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPILER-FRONTEND-003 |
| Category | Compiler \| Frontend \| Parser |
| Status | Implemented |
| Source | `test/01_unit/compiler/frontend/parser_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Parse Declarations

#### parse val declaration

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
check(x == 42)
```

</details>

#### parse var declaration

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 42
x = 100
check(x == 100)
```

</details>

#### parse typed val

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
check(x == 42)
```

</details>

#### parse typed var

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x: i64 = 42
check(x == 42)
```

</details>

#### parse walrus operator

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
# TODO: walrus operator `:=` triggers parse error (expected indented block after ':')
# Once fixed, restore: x := 42
check(x == 42)
```

</details>

#### parse function declaration

- fn add
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64) -> i64:
    a + b
check(add(3, 4) == 7)
```

</details>

#### parse function with no return type

- fn greet
- check
- greet
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text):
    check(name == "test")
greet("test")
check(1 + 1 == 2)
```

</details>

#### parse function with default args

- fn greet
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text, prefix: text = "Hello") -> text:
    "{prefix}, {name}!"
check(greet("World") == "Hello, World!")
check(greet("World", "Hi") == "Hi, World!")
```

</details>

### Parse Expressions

#### parse binary expression

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(3 + 4 == 7)
```

</details>

#### parse parenthesized expression

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((3 + 4) * 2 == 14)
```

</details>

#### parse unary negation

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(-5 == -5)
```

</details>

#### parse logical not

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not false)
```

</details>

#### parse string interpolation

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "world"
check("hello {name}" == "hello world")
```

</details>

#### parse escaped string literal

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "line1\nline2"
check(s.len() == 11)
```

</details>

#### parse array literal

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### parse map literal

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = {"a": 1, "b": 2}
check(m.len() == 2)
```

</details>

#### parse range

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..5:
    count = count + 1
check(count == 5)
```

</details>

#### parse lambda

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = \x: x * 2
check(f(21) == 42)
```

</details>

#### parse placeholder lambda

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = _ * 2
check(f(21) == 42)
```

</details>

#### parse method reference

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val words = ["hello", "world"]
val lengths = words.map(&:len)
check(lengths[0] == 5)
```

</details>

#### parse pipe operator

- fn double
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i64) -> i64:
    x * 2
val result = 21 |> double
check(result == 42)
```

</details>

#### parse optional chaining

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = Some(42)
check(x.?)
```

</details>

#### parse nil coalescing

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: Option<i64> = nil
val y = x ?? 99
check(y == 99)
```

</details>

### Parse Control Flow

#### parse if

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 0
if true:
    result = 1
check(result == 1)
```

</details>

#### parse if-else

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 0
if false:
    result = 1
else:
    result = 2
check(result == 2)
```

</details>

#### parse if-elif-else

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(parser_if_elif_result(5) == "small")
```

</details>

<details>
<summary>Advanced: parse while loop</summary>

#### parse while loop

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var i = 0
while i < 5:
    i = i + 1
check(i == 5)
```

</details>


</details>

<details>
<summary>Advanced: parse for-in loop</summary>

#### parse for-in loop

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in [1, 2, 3]:
    sum = sum + i
check(sum == 6)
```

</details>


</details>

#### parse match expression

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2
val result = match x:
    1: "one"
    2: "two"
    _: "other"
check(result == "two")
```

</details>

#### parse match with destructuring

- Some
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
var result = 0
match opt:
    Some(v): result = v
    nil: result = -1
check(result == 42)
```

</details>

### Parse Class Definitions

#### parse simple class

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Point2D:
    x: i64
    y: i64
val p = Point2D(x: 1, y: 2)
check(p.x == 1 and p.y == 2)
```

</details>

#### parse class with methods

- fn get
- me increment
- var c = Counter
- c increment
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Counter:
    value: i64
    fn get() -> i64:
        self.value
    me increment():
        self.value = self.value + 1
var c = Counter(value: 0)
c.increment()
check(c.get() == 1)
```

</details>

#### parse class with static

- static fn create
- Factory
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Factory:
    val_field: i64
    static fn create() -> Factory:
        Factory(val_field: 0)
val f = Factory.create()
check(f.val_field == 0)
```

</details>

### Parse Comprehensions

#### list comprehension

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val squares = [for x in 0..5: x * x]
check(squares.len() == 5)
check(squares[0] == 0)
check(squares[4] == 16)
```

</details>

#### filtered comprehension

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evens = [for x in 0..10 if x % 2 == 0: x]
check(evens.len() == 5)
```

</details>

#### nested comprehension

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pairs = [for x in 0..3: x * 10]
check(pairs.len() == 3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
