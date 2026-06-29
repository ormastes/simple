# Classes and Object-Oriented Programming Specification

> Tests for class definitions, instance creation, field access, methods, impl blocks, context blocks, method_missing, auto-forwarding properties, and static polymorphism with interface bindings.

<!-- sdn-diagram:id=classes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=classes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

classes_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=classes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Classes and Object-Oriented Programming Specification

Tests for class definitions, instance creation, field access, methods, impl blocks, context blocks, method_missing, auto-forwarding properties, and static polymorphism with interface bindings.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OOP-001 |
| Category | Language \| Classes |
| Status | Implemented |
| Source | `test/03_system/feature/usage/classes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for class definitions, instance creation, field access, methods,
impl blocks, context blocks, method_missing, auto-forwarding properties,
and static polymorphism with interface bindings.

## Syntax

```simple
class Calculator:
static fn add(a, b):
return a + b

struct Point:
x: i64
y: i64

impl Point:
fn sum(self):
return self.x + self.y

context obj:
method()  # Dispatches to obj.method()
```

## Scenarios

### Static Class Methods

#### calls static method on class

1. static fn add
2. expect Calculator add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Calculator:
    static fn add(a, b):
        return a + b

expect Calculator.add(3, 4) == 7
```

</details>

#### calls multiple static methods

1. static fn double
2. static fn triple
3. expect Math double


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Math:
    static fn double(x):
        return x * 2

    static fn triple(x):
        return x * 3

expect Math.double(5) + Math.triple(4) == 22
```

</details>

### Impl Blocks

#### adds method to struct via impl

1. fn sum
2. expect p sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Block-scoped impl now works!
struct Point:
    x: i64
    y: i64

impl Point:
    fn sum(self):
        return self.x + self.y

val p = Point { x: 15, y: 25 }
expect p.sum() == 40
```

</details>

#### adds method with arguments via impl

1. fn add
2. expect c add


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Block-scoped impl now works!
struct Counter:
    value: i64

impl Counter:
    fn add(self, n):
        return self.value + n

val c = Counter { value: 10 }
expect c.add(5) == 15
```

</details>

### Class Instantiation

#### creates instances with direct construction

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Person:
    name: text
    age: i64

val p = Person { name: "Alice", age: 30 }
expect p.age == 30
```

</details>

#### accesses string field

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Greeting:
    message: text

val g = Greeting { message: "Hello" }
var result = 0
if g.message == "Hello":
    result = 1
expect result == 1
```

</details>

#### creates class with default field values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Counter:
    count: i64

val c = Counter(count: 0)
expect c.count == 0
```

</details>

### Instance Methods

#### calls instance method

1. fn get double
2. expect b get double


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Box:
    value: i64

    fn get_double(self):
        return self.value * 2

val b = Box { value: 21 }
expect b.get_double() == 42
```

</details>

#### calls method with arguments

1. fn add
2. expect a add


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Adder:
    base: i64

    fn add(self, x):
        return self.base + x

val a = Adder { base: 10 }
expect a.add(5) == 15
```

</details>

### Context Blocks

#### dispatches method to context object

1. fn double
2. res = double


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Block-scoped context now works!
class Calculator:
    fn double(self, x):
        return x * 2

val calc = Calculator {}
var res = 0
context calc:
    res = double(21)
expect res == 42
```

</details>

#### accesses self fields in context method

1. fn add
2. res = add


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Block-scoped context now works!
class Adder:
    base: i64 = 10

    fn add(self, x):
        return self.base + x

val a = Adder { base: 30 }
var res = 0
context a:
    res = add(12)
expect res == 42
```

</details>

### Method Missing

#### calls method_missing for unknown method

1. fn method missing
2. expect d unknown method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class DSL:
    fn method_missing(self, name, args, block):
        return 42

val d = DSL {}
expect d.unknown_method() == 42
```

</details>

#### passes arguments to method_missing

1. fn method missing
2. expect m any method


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Multiplier:
    factor: i64 = 10

    fn method_missing(self, name, args, block):
        val x = args[0]
        return self.factor * x

val m = Multiplier { factor: 7 }
expect m.any_method(6) == 42
```

</details>

#### uses method_missing in context block

1. fn method missing
2. res = something undefined


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Block-scoped context now works!
class Counter:
    count: i64 = 0

    fn method_missing(self, name, args, block):
        return 42

val c = Counter { count: 0 }
var res = 0
context c:
    res = something_undefined()
expect res == 42
```

</details>

### Auto-Forwarding Properties

#### gets property via get_ method

1. fn get name


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Person:
    fn get_name(self) -> text:
        return self._name

val p = Person { _name: "Alice" }
var result = 0
if p.get_name() == "Alice":
    result = 1
expect result == 1
```

</details>

#### sets property via set_ method returning new instance

1. fn get value
2. fn set value
3. expect c2 get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class ValueHolder:
    fn get_value(self) -> i64:
        return self._value

    fn set_value(self, v: i64) -> ValueHolder:
        return ValueHolder { _value: v }

val c = ValueHolder { _value: 10 }
val c2 = c.set_value(42)
expect c2.get_value() == 42
```

</details>

#### checks boolean property via is_ method

1. fn is active


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Item:
    fn is_active(self) -> bool:
        return self._active

val item = Item { _active: true }
var result = 0
if item.is_active():
    result = 1
expect result == 1
```

</details>

#### uses combined getter and setter

1. fn get content
2. fn set content
3. expect b2 get content


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class ContentBox:
    fn get_content(self) -> i64:
        return self._content

    fn set_content(self, v: i64) -> ContentBox:
        return ContentBox { _content: v }

val b = ContentBox { _content: 0 }
val b2 = b.set_content(100)
expect b2.get_content() == 100
```

</details>

### Static Polymorphism

#### binds trait to concrete class

1. fn log
2. fn log
3. fn create logger


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Logger:
    fn log(self, msg: text) -> text

class ConsoleLogger:
    fn log(self, msg: text) -> text:
        return "Console: " + msg

bind Logger = ConsoleLogger

fn create_logger() -> Logger:
    return ConsoleLogger {}

val logger: Logger = create_logger()
val res = logger.log("Hello")
var result = 0
if res == "Console: Hello":
    result = 1
expect result == 1
```

</details>

#### binds trait with multiple methods

1. fn add
2. fn multiply
3. fn add
4. fn multiply
5. expect calc add


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Calculator:
    fn add(self, a: i64, b: i64) -> i64
    fn multiply(self, a: i64, b: i64) -> i64

class SimpleCalc:
    fn add(self, a: i64, b: i64) -> i64:
        return a + b
    fn multiply(self, a: i64, b: i64) -> i64:
        return a * b

bind Calculator = SimpleCalc

val calc: Calculator = SimpleCalc {}
expect calc.add(3, 4) + calc.multiply(2, 5) == 17
```

</details>

#### binds trait with fields

1. fn get value
2. fn increment
3. fn get value
4. fn increment
5. expect counter get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Counter:
    fn get_value(self) -> i64
    fn increment(self) -> i64

class SimpleCounter:
    value: i64

    fn get_value(self) -> i64:
        return self.value

    fn increment(self) -> i64:
        return self.value + 1

bind Counter = SimpleCounter

val counter: Counter = SimpleCounter { value: 42 }
expect counter.get_value() == 42
```

</details>

#### passes bound trait as function parameter

1. fn greet
2. fn greet
3. fn do greeting
4. expect do greeting


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Greeter:
    fn greet(self, name: text) -> i64

class FormalGreeter:
    multiplier: i64

    fn greet(self, name: text) -> i64:
        return self.multiplier * 10

bind Greeter = FormalGreeter

fn do_greeting(g: Greeter) -> i64:
    return g.greet("Alice")

val greeter: Greeter = FormalGreeter { multiplier: 5 }
expect do_greeting(greeter) == 50
```

</details>

### Trait Polymorphism

#### calculates different areas via Shape trait

1. fn area
2. fn area
3. fn area
4. expect s area


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Block-scoped impl Trait for Type now works!
trait Shape:
    fn area(self) -> i64

struct Square:
    side: i64

struct Rectangle:
    width: i64
    height: i64

impl Shape for Square:
    fn area(self) -> i64:
        return self.side * self.side

impl Shape for Rectangle:
    fn area(self) -> i64:
        return self.width * self.height

val s = Square { side: 5 }
val r = Rectangle { width: 4, height: 3 }
expect s.area() + r.area() == 37
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
