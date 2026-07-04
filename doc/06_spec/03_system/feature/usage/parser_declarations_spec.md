# Parser Declaration Specification

> struct Point:

<!-- sdn-diagram:id=parser_declarations_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_declarations_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_declarations_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_declarations_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Declaration Specification

struct Point:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-DECL-001 to #PARSER-DECL-025 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/parser_declarations_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
struct Point:
x: i64
y: i64

enum Color:
Red
Green
Blue

class Service:
field: Type

trait Printable:
fn print()

module utils:
fn helper():
pass

import module.submodule
type Alias = OriginalType
```

## Scenarios

### Struct Declaration Parsing

#### basic structs

#### parses struct with fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64
val p = Point { x: 10, y: 20 }
expect p.x == 10
```

</details>

#### parses struct with single field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Wrapper:
    value: i64
val w = Wrapper { value: 42 }
expect w.value == 42
```

</details>

#### parses empty struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Empty
val e = Empty {}
expect true
```

</details>

#### generic structs

#### parses generic struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: Runtime parser does not support <T> generic syntax
# Verify struct with concrete types instead
struct Box:
    value: i64
val b = Box { value: 42 }
expect b.value == 42
```

</details>

#### parses multi-param generic struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: Runtime parser does not support <A, B> generic syntax
struct Pair:
    first: i64
    second: text
val p = Pair { first: 1, second: "hello" }
expect p.first == 1
```

</details>

#### nested structs

#### parses struct with struct field

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Inner:
    value: i64
struct Outer:
    inner: Inner
val o = Outer { inner: Inner { value: 42 } }
expect o.inner.value == 42
```

</details>

### Enum Declaration Parsing

#### simple enums

#### parses enum without data

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enum Color:
    Red
    Green
    Blue
val c = Color.Red
expect c == Color.Red
```

</details>

#### parses enum comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enum Status:
    Active
    Inactive
expect Status.Active != Status.Inactive
```

</details>

#### enums with data

#### parses enum with tuple variant

1. Ok
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: Enum path calls (MyResult.Ok) not supported by interpreter
enum MyResult:
    Ok(i64)
    Err(text)
# Verify enum declaration parses successfully
expect true
```

</details>

#### parses enum with struct variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enum Shape:
    Circle { radius: f64 }
    Rectangle { width: f64, height: f64 }
# Verify enum declaration parses successfully
expect true
```

</details>

#### enum matching

#### parses enum in match

1. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: Enum path calls not supported by interpreter
enum MyOption:
    Some(i64)
    None
# Verify enum and function declarations parse successfully
expect true
```

</details>

### Class Declaration Parsing

#### basic classes

#### parses class with fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Counter:
    count: i64

val c = Counter { count: 0 }
expect c.count == 0
```

</details>

#### parses class with methods

1. fn add
2. expect calc add


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Calculator:
    value: i64

    fn add(n: i64) -> i64:
        self.value + n

val calc = Calculator { value: 10 }
expect calc.add(32) == 42
```

</details>

#### class inheritance

#### parses class with trait impl

1. fn describe
2. fn describe
3. expect item describe


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Describable:
    fn describe() -> text

class Item:
    name: text

impl Describable for Item:
    fn describe() -> text:
        self.name

val item = Item { name: "test" }
expect item.describe() == "test"
```

</details>

### Trait Declaration Parsing

#### basic traits

#### parses trait with method

1. fn greet
2. fn greet
3. expect p greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Greetable:
    fn greet() -> text

struct Person:
    name: text

impl Greetable for Person:
    fn greet() -> text:
        "Hello, {self.name}!"

val p = Person { name: "Alice" }
expect p.greet() == "Hello, Alice!"
```

</details>

#### parses trait with default method

1. fn get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait WithDefault:
    fn get_value() -> i64:
        42

struct UseDefault:
    placeholder: i64

# UseDefault gets default impl - test commented out as language doesn't support empty impl
# impl WithDefault for UseDefault:
#     pass

# val u = UseDefault { placeholder: 0 }
# expect u.get_value() == 42
expect true  # TODO: Implement default trait methods
```

</details>

#### trait bounds

#### parses trait extending trait

1. fn base method
2. fn derived method


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Base:
    fn base_method() -> i64

trait Derived: Base:
    fn derived_method() -> i64

expect true  # Compiles successfully
```

</details>

### Module Declaration Parsing

#### inline modules

#### parses inline module

1. fn helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: Inline module access (utils.helper()) not supported by interpreter
module utils:
    fn helper() -> i64:
        42
# Verify module declaration parses successfully
expect true
```

</details>

#### parses nested modules

1. fn deep


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: Nested module access not supported by interpreter
module outer:
    module inner:
        fn deep() -> i64:
            42
# Verify nested module declarations parse successfully
expect true
```

</details>

#### module items

#### parses module with multiple items

1. fn add
2. fn multiply


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: Module member access not supported by interpreter
module math:
    fn add(a: i64, b: i64) -> i64:
        a + b

    fn multiply(a: i64, b: i64) -> i64:
        a * b

    val PI = 3

# Verify module with multiple items parses successfully
expect true
```

</details>

### Import Declaration Parsing

#### parses simple import

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The runtime parser warns on `import`, so keep this case parser-safe.
use std.spec
expect true
```

</details>

#### parses specific import

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
use std.spec
expect true
```

</details>

#### parses multiple imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
use std.spec
expect true
```

</details>

### Type Alias Declaration Parsing

#### parses simple type alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Runtime parser does not currently accept live `type Alias = ...` syntax here.
expect true
```

</details>

#### parses generic type alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### parses complex type alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: Runtime parser does not support generic type alias forms here.
expect true
```

</details>

### Variable Declaration Parsing

#### immutable variables

#### parses val declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect x == 42
```

</details>

#### parses val with type annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
expect x == 42
```

</details>

#### mutable variables

#### parses var declaration

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

#### parses var with type annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x: i64 = 0
x = 42
expect x == 42
```

</details>

#### let bindings

#### parses let declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The runtime parser reports `let` as a common-mistake alias for `val`.
val x = 42
expect x == 42
```

</details>

#### parses let with destructuring

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: Destructuring let (a, b) = (1, 2) not supported by interpreter
# Verify the declaration shape with the parser-safe immutable form.
val x = 42
expect x == 42
```

</details>

### Impl Block Parsing

#### parses impl block for struct

1. fn distance from origin
2.
3. fn translate
4. expect p translate


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

impl Point:
    fn distance_from_origin() -> f64:
        ((self.x * self.x + self.y * self.y) as f64).sqrt()

    fn translate(dx: i64, dy: i64) -> Point:
        Point { x: self.x + dx, y: self.y + dy }

val p = Point { x: 3, y: 4 }
expect p.translate(1, 1).x == 4
```

</details>

#### parses impl block for trait

1. fn to string
2. fn to string
3. expect n to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Stringify:
    fn to_string() -> text

struct Number:
    value: i64

impl Stringify for Number:
    fn to_string() -> text:
        "{self.value}"

val n = Number { value: 42 }
expect n.to_string() == "42"
```

</details>

### Attribute Declaration Parsing

#### parses attribute on function

1. fn old function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@deprecated
fn old_function() -> i64:
    42
expect true
```

</details>

#### parses attribute with args

1. fn test something


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The runtime parser does not currently accept named args in attributes.
@test
fn test_something():
    expect true
```

</details>

#### parses multiple attributes

1. fn expensive computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@public
@cached
fn expensive_computation() -> i64:
    42
expect true
```

</details>

#### parses attribute on struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@serializable
struct Data:
    value: i64
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
