# Classes and Object-Oriented Programming Specification

> Tests for class definitions, instance creation, field access, methods, impl blocks, context blocks, method_missing, auto-forwarding properties, and static polymorphism with interface bindings.

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
| Source | `test/feature/usage/classes_spec.spl` |
| Updated | 2026-08-26 |
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
use std.spec.step

fn sum(self):
return self.x + self.y

context obj:
method()  # Dispatches to obj.method()
```

## Scenarios

### Static Class Methods

#### calls static method on class

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- calls static method on class


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls static method on class")
class Calculator:
    static fn add(a, b):
        return a + b

expect Calculator.add(3, 4) == 7
```

</details>

#### calls multiple static methods

- calls multiple static methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls multiple static methods")
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

- adds method to struct via impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds method to struct via impl")
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

- adds method with arguments via impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds method with arguments via impl")
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

- creates instances with direct construction


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates instances with direct construction")
class Person:
    name: text
    age: i64

val p = Person { name: "Alice", age: 30 }
expect p.age == 30
```

</details>

#### accesses string field

- accesses string field


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accesses string field")
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

- creates class with default field values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates class with default field values")
class Counter:
    count: i64

val c = Counter(count: 0)
expect c.count == 0
```

</details>

### Instance Methods

#### calls instance method

- calls instance method


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls instance method")
class Box:
    value: i64

    fn get_double(self):
        return self.value * 2

val b = Box { value: 21 }
expect b.get_double() == 42
```

</details>

#### calls method with arguments

- calls method with arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls method with arguments")
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

- dispatches method to context object


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dispatches method to context object")
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

- accesses self fields in context method


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accesses self fields in context method")
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

- calls method_missing for unknown method


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls method_missing for unknown method")
class DSL:
    fn method_missing(self, name, args, block):
        return 42

val d = DSL {}
expect d.unknown_method() == 42
```

</details>

#### passes arguments to method_missing

- passes arguments to method_missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes arguments to method_missing")
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

- uses method_missing in context block


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses method_missing in context block")
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

- gets property via get_ method


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("gets property via get_ method")
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

- sets property via set_ method returning new instance


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sets property via set_ method returning new instance")
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

- checks boolean property via is_ method


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("checks boolean property via is_ method")
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

- uses combined getter and setter


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses combined getter and setter")
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

- binds trait to concrete class


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds trait to concrete class")
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

- binds trait with multiple methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds trait with multiple methods")
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

- binds trait with fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds trait with fields")
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

- passes bound trait as function parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes bound trait as function parameter")
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

- calculates different areas via Shape trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calculates different areas via Shape trait")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6a5692b6a0a7a0706b6ae4647bab41bcd8c18893ef79dd5c38e8b630ab641fab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6a5692b6a0a7a0706b6ae4647bab41bcd8c18893ef79dd5c38e8b630ab641fab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6a5692b6a0a7a0706b6ae4647bab41bcd8c18893ef79dd5c38e8b630ab641fab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/classes_spec.spl
mirror: doc/06_spec/feature/usage/classes_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/classes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/classes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/classes_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls static method on class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/classes_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls multiple static methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/classes_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds method to struct via impl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
