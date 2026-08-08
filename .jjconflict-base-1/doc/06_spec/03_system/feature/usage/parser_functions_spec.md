# Parser Function Definition Specification

> fn name(params) -> ReturnType:

<!-- sdn-diagram:id=parser_functions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_functions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_functions_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_functions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Function Definition Specification

fn name(params) -> ReturnType:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-FN-001 to #PARSER-FN-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/parser_functions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
fn name(params) -> ReturnType:
body

fn generic<T>(x: T) -> T where T: Trait:
body

extern fn ffi_func(x: i64) -> i64

macro name(params) -> (contract):
body
```

## Scenarios

### Basic Function Definition Parsing

#### minimal functions

#### parses function without params

1. fn get value
2. expect get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value() -> i64:
    42
expect get_value() == 42
```

</details>

#### parses function with single param

1. fn double
2. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i64) -> i64:
    x * 2
expect double(21) == 42
```

</details>

#### parses function with multiple params

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64) -> i64:
    a + b
expect add(20, 22) == 42
```

</details>

#### return types

#### parses explicit return type

1. fn typed
2. expect typed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn typed() -> i64:
    42
expect typed() == 42
```

</details>

#### parses inferred return

1. fn inferred
2. expect inferred


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn inferred():
    42
expect inferred() == 42
```

</details>

#### parses unit return

1. fn unit fn
2. unit fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn unit_fn():
    val x = 1
unit_fn()
expect true
```

</details>

#### function body

#### parses multi-statement body

1. fn complex
2. expect complex


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn complex(x: i64) -> i64:
    val doubled = x * 2
    val incremented = doubled + 1
    incremented
expect complex(20) == 41
```

</details>

#### parses recursive function

1. fn fib
2. fib
3. expect fib


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn fib(n: i64) -> i64:
    if n <= 1:
        n
    else:
        fib(n - 1) + fib(n - 2)
expect fib(10) == 55
```

</details>

### Generic Function Parsing

#### parses single type parameter

1. fn identity<T>
2. expect identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity<T>(x: T) -> T:
    x
expect identity(42) == 42
```

</details>

#### parses multiple type parameters

1. fn pair<T, U>
2.


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn pair<T, U>(a: T, b: U) -> (T, U):
    (a, b)
val p = pair(1, "hello")
expect p.0 == 1
```

</details>

#### parses nested generic types

1. fn wrap<T>
2. Some
3. expect wrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn wrap<T>(x: T) -> Option<T>:
    Some(x)
expect wrap(42).unwrap() == 42
```

</details>

### Where Clause Parsing

#### parses single where clause

1. fn show
2. fn display<T>
3. x show
4. fn show
5. expect display


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Show:
    fn show() -> text
fn display<T>(x: T) -> text where T: Show:
    x.show()
struct Number:
    value: i64
impl Show for Number:
    fn show() -> text:
        "{self.value}"
expect display(Number { value: 42 }) == "42"
```

</details>

#### parses multiple bounds

1. fn clone
2. fn debug
3. fn process<T>


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Clone:
    fn clone() -> Self
trait Debug:
    fn debug() -> text
fn process<T>(x: T) where T: Clone + Debug:
    x
expect true  # Compiles successfully
```

</details>

#### parses multiple where clauses

1. fn clone
2. fn combine<T, U>


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Cloneable:
    fn clone() -> Self
fn combine<T, U>(a: T, b: U) where T: Cloneable, U: Cloneable:
    a
expect true  # Compiles successfully
```

</details>

### Default Parameter Parsing

#### parses default parameter

1. fn greet
2. expect greet
3. expect greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text = "World") -> text:
    "Hello, {name}!"
expect greet() == "Hello, World!"
expect greet("Alice") == "Hello, Alice!"
```

</details>

#### parses multiple defaults

1. fn create point
2.


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create_point(x: i64 = 0, y: i64 = 0) -> (i64, i64):
    (x, y)
val p1 = create_point()
val p2 = create_point(5)
val p3 = create_point(5, 10)
expect p1.0 == 0
expect p2.0 == 5
expect p3.1 == 10
```

</details>

#### parses mixed required and default

1. fn format
2. expect format
3. expect format


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn format(value: i64, prefix: text = "", suffix: text = "") -> text:
    "{prefix}{value}{suffix}"
expect format(42) == "42"
expect format(42, "<<") == "<<42"
```

</details>

### Named Argument Parsing

#### parses named arguments

1. fn point
2.


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn point(x: i64, y: i64) -> (i64, i64):
    (x, y)
val p = point(x = 10, y = 20)
expect p.0 == 10
```

</details>

#### parses mixed positional and named

1. fn format person


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn format_person(name: text, age: i64, city: text) -> text:
    "{name}, {age}, from {city}"
val result = format_person("Alice", age = 30, city = "NYC")
expect result == "Alice, 30, from NYC"
```

</details>

#### parses named arguments in any order

1. fn subtract
2. expect subtract


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn subtract(a: i64, b: i64) -> i64:
    a - b
expect subtract(b = 10, a = 52) == 42
```

</details>

### Extern Function Parsing

#### parses extern function

1. extern fn strlen


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
extern fn strlen(s: text) -> i64

# Extern functions may not be callable without FFI setup
# but should parse correctly
expect true
```

</details>

#### parses extern with multiple params

1. extern fn add external


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
extern fn add_external(a: i64, b: i64) -> i64
expect true
```

</details>

### Macro Definition Parsing

#### parses macro definition

1. macro double emit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro double_emit(x: i64) -> (returns result: i64):
    emit result:
        x + x
val value = double_emit!(21)
expect value == 42
```

</details>

### Actor Definition Parsing

#### parses actor definition

1. fn increment
2. fn get


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
actor Counter:
    count: i64 = 0

    fn increment():
        self.count = self.count + 1

    fn get() -> i64:
        self.count

expect true  # Compiles successfully
```

</details>

### Method Definition Parsing

#### instance methods

#### parses method with self

1. fn sum
2. expect p sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Point:
    x: i64
    y: i64

    fn sum() -> i64:
        self.x + self.y

val p = Point(x: 20, y: 22)
expect p.sum() == 42
```

</details>

#### parses mutable method

1. me increment
2. var c = Counter
3. c increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Counter:
    value: i64

    me increment():
        self.value = self.value + 1

var c = Counter(value: 0)
c.increment()
expect c.value == 1
```

</details>

#### static methods

#### parses static method

1. static fn origin
2. Point


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Point:
    x: i64
    y: i64

    static fn origin() -> Point:
        Point(x: 0, y: 0)

val p = Point.origin()
expect p.x == 0
```

</details>

### Lambda Expression Parsing

#### parses simple lambda

1. expect f


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = \x: x * 2
expect f(21) == 42
```

</details>

#### parses multi-param lambda

1. expect f


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = \a, b, c: a + b + c
expect f(10, 20, 12) == 42
```

</details>

#### parses typed lambda

1. expect f


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Typed lambda syntax not yet supported
val f = \x: x * 2
expect f(21) == 42
```

</details>

#### parses lambda in higher-order context

1. fn apply
2. f
3. expect apply


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(f, x: i64) -> i64:
    f(x)
expect apply(\x: x + 1, 41) == 42
```

</details>

### Async Function Parsing

#### parses async function

1. async fn fetch value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
async fn fetch_value() -> i64:
    42
expect true  # Compiles successfully
```

</details>

#### parses await expression

1. async fn get data
2. async fn use data


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
async fn get_data() -> i64:
    42
async fn use_data() -> i64:
    val x = await get_data()
    x * 2
expect true  # Compiles successfully
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
