# Traits Specification

> Traits define shared behavior that types can implement, enabling polymorphism and code reuse. They are similar to interfaces in other languages but support default implementations, associated types, and trait bounds for generics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traits Specification

Traits define shared behavior that types can implement, enabling polymorphism and code reuse. They are similar to interfaces in other languages but support default implementations, associated types, and trait bounds for generics.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/feature/usage/traits_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Traits define shared behavior that types can implement, enabling polymorphism
and code reuse. They are similar to interfaces in other languages but support
default implementations, associated types, and trait bounds for generics.

## Syntax

```simple
trait Printable:
use std.spec.step

fn print(self)

trait Addable:
fn add(self, other: Self) -> Self

fn double(self) -> Self:  # Default implementation
self.add(self)

impl Printable for Point:
fn print(self):
print("({x}, {y})")
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Trait | Interface defining shared behavior |
| Implementation | Concrete behavior for a specific type |
| Default Method | Trait method with provided implementation |
| Trait Bound | Generic constraint requiring trait implementation |

## Behavior

- Traits define method signatures types must implement
- Default methods provide optional implementations
- Types can implement multiple traits
- Trait bounds constrain generic type parameters

## Scenarios

### Traits

#### basic trait implementation

#### implements trait for struct

- implements trait for struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("implements trait for struct")
trait Summable:
    fn sum(self):
        return 0

struct Point:
    x: i64
    y: i64

impl Summable for Point:
    fn sum(self):
        return self.x + self.y

val p = Point { x: 10, y: 20 }
expect p.sum() == 30
```

</details>

#### implements trait with arguments

- implements trait with arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("implements trait with arguments")
trait Calculator:
    fn add(self, n):
        return 0

struct Counter:
    value: i64

impl Calculator for Counter:
    fn add(self, n):
        return self.value + n

val c = Counter { value: 50 }
expect c.add(25) == 75
```

</details>

#### multiple trait implementations

#### allows multiple types to implement same trait

- allows multiple types to implement same trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows multiple types to implement same trait")
trait Valuable:
    fn value(self):
        return 0

struct Coin:
    amount: i64

struct Bill:
    amount: i64

impl Valuable for Coin:
    fn value(self):
        return self.amount

impl Valuable for Bill:
    fn value(self):
        return self.amount * 100

val c = Coin { amount: 5 }
val b = Bill { amount: 2 }
expect c.value() + b.value() == 205
```

</details>

#### multiple traits on one type

#### type implements two different traits

- type implements two different traits


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("type implements two different traits")
trait Nameable:
    fn get_name(self) -> text:
        return ""

trait Scorable:
    fn get_score(self) -> i64:
        return 0

struct Player:
    name: text
    score: i64

impl Nameable for Player:
    fn get_name(self) -> text:
        return self.name

impl Scorable for Player:
    fn get_score(self) -> i64:
        return self.score

val p = Player { name: "Alice", score: 99 }
expect p.get_name() == "Alice"
expect p.get_score() == 99
```

</details>

#### type implements three traits

- type implements three traits


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("type implements three traits")
trait HasId:
    fn id(self) -> i64:
        return 0

trait HasLabel:
    fn label(self) -> text:
        return ""

trait HasPriority:
    fn priority(self) -> i64:
        return 0

struct Task:
    tid: i64
    name: text
    prio: i64

impl HasId for Task:
    fn id(self) -> i64:
        return self.tid

impl HasLabel for Task:
    fn label(self) -> text:
        return self.name

impl HasPriority for Task:
    fn priority(self) -> i64:
        return self.prio

val t = Task { tid: 1, name: "deploy", prio: 5 }
expect t.id() == 1
expect t.label() == "deploy"
expect t.priority() == 5
```

</details>

### Default Trait Methods

#### uses default trait method when not overridden

- uses default trait method when not overridden


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses default trait method when not overridden")
trait Greeter:
    fn greet(self) -> i64
    fn farewell(self) -> i64:
        return 99

struct Person:
    name: str

impl Greeter for Person:
    fn greet(self) -> i64:
        return 42

val p = Person { name: "Alice" }
expect p.farewell() == 99
```

</details>

#### allows overriding default trait method

- allows overriding default trait method


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows overriding default trait method")
trait Greeter:
    fn greet(self) -> i64
    fn farewell(self) -> i64:
        return 99

struct Person:
    name: str

impl Greeter for Person:
    fn greet(self) -> i64:
        return 42
    fn farewell(self) -> i64:
        return 7

val p = Person { name: "Bob" }
expect p.farewell() == 7
```

</details>

#### default method can call abstract method

- default method can call abstract method


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("default method can call abstract method")
trait Calculator:
    fn compute(self) -> i64
    fn double(self) -> i64:
        return self.compute() * 2

struct Value:
    n: i64

impl Calculator for Value:
    fn compute(self) -> i64:
        return self.n

val v = Value { n: 21 }
expect v.double() == 42
```

</details>

#### default method can call other default method

- default method can call other default method


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("default method can call other default method")
trait Chainable:
    fn base(self) -> i64:
        return 1
    fn step(self) -> i64:
        return self.base() * 10
    fn final_val(self) -> i64:
        return self.step() + 5

struct Unit:
    x: i64

impl Chainable for Unit:
    fn base(self) -> i64:
        return self.x

val u = Unit { x: 3 }
expect u.base() == 3
expect u.step() == 30
expect u.final_val() == 35
```

</details>

### Dynamic Trait Objects

#### coerces concrete type to dyn Trait via let binding

- coerces concrete type to dyn Trait via let binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("coerces concrete type to dyn Trait via let binding")
trait Drawable:
    fn draw(self) -> i64

struct Circle:
    radius: i64

impl Drawable for Circle:
    fn draw(self) -> i64:
        return self.radius * 3

val c = Circle { radius: 7 }
val drawable: dyn Drawable = c
expect drawable.draw() == 21
```

</details>

#### passes concrete type to dyn Trait parameter

- passes concrete type to dyn Trait parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes concrete type to dyn Trait parameter")
trait Shape:
    fn area(self) -> i64

struct Square:
    side: i64

impl Shape for Square:
    fn area(self) -> i64:
        return self.side * self.side

fn process_shape(s: dyn Shape) -> i64:
    return s.area()

val sq = Square { side: 6 }
expect process_shape(sq) == 36
```

</details>

#### handles multiple types via dyn Trait

- handles multiple types via dyn Trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles multiple types via dyn Trait")
trait Describable:
    fn value(self) -> i64

struct A:
    x: i64

struct B:
    y: i64

impl Describable for A:
    fn value(self) -> i64:
        return self.x * 10

impl Describable for B:
    fn value(self) -> i64:
        return self.y + 100

fn get_value(d: dyn Describable) -> i64:
    return d.value()

val a = A { x: 5 }
val b = B { y: 7 }
expect get_value(a) + get_value(b) == 157
```

</details>

#### dyn Trait with default method

- dyn Trait with default method


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dyn Trait with default method")
trait Greetable:
    fn hello(self) -> i64:
        return 42
    fn custom(self) -> i64

struct Greeter:
    n: i64

impl Greetable for Greeter:
    fn custom(self) -> i64:
        return self.n

val g = Greeter { n: 7 }
val dg: dyn Greetable = g
expect dg.hello() == 42
expect dg.custom() == 7
```

</details>

### Trait and Mixin Integration

#### trait impl accesses mixin fields

- trait impl accesses mixin fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("trait impl accesses mixin fields")
trait Computable:
    fn compute(self) -> i64:
        return 0

mixin HasData:
    data: i64

class Worker:
    use HasData
    factor: i64

impl Computable for Worker:
    fn compute(self) -> i64:
        return self.data * self.factor

val w = Worker(data: 7, factor: 3)
expect w.compute() == 21
```

</details>

#### multiple traits on class with mixin

- multiple traits on class with mixin


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiple traits on class with mixin")
trait Labelable:
    fn get_label(self) -> text:
        return ""

trait Rankable:
    fn get_rank(self) -> i64:
        return 0

mixin Identified:
    id: i64

class Hero:
    use Identified
    name: text
    power: i64

impl Labelable for Hero:
    fn get_label(self) -> text:
        return "{self.name} #{self.id}"

impl Rankable for Hero:
    fn get_rank(self) -> i64:
        return self.power

val h = Hero(id: 1, name: "Zara", power: 95)
expect h.get_label() == "Zara #1"
expect h.get_rank() == 95
```

</details>

#### dyn Trait dispatch on mixin class

- dyn Trait dispatch on mixin class


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dyn Trait dispatch on mixin class")
trait Measurable:
    fn measure(self) -> i64:
        return 0

mixin Sized:
    width: i64
    height: i64

class Rect:
    use Sized

impl Measurable for Rect:
    fn measure(self) -> i64:
        return self.width * self.height

fn get_measure(m: dyn Measurable) -> i64:
    return m.measure()

val r = Rect(width: 5, height: 8)
expect get_measure(r) == 40
```

</details>

#### mixin method and trait method coexist

- mixin method and trait method coexist


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mixin method and trait method coexist")
trait Taggable:
    fn tag(self) -> text:
        return ""

mixin Scored:
    score: i64

    fn get_score() -> i64:
        return self.score

class Entry:
    use Scored
    label: text

impl Taggable for Entry:
    fn tag(self) -> text:
        return self.label

val e = Entry(score: 88, label: "gold")
expect e.get_score() == 88
expect e.tag() == "gold"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `f01bc97167b868975eeb88d26eb7016d4301807c26950b70dd47d025d55ee92f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f01bc97167b868975eeb88d26eb7016d4301807c26950b70dd47d025d55ee92f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f01bc97167b868975eeb88d26eb7016d4301807c26950b70dd47d025d55ee92f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/traits_spec.spl
mirror: doc/06_spec/feature/usage/traits_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/traits_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/traits_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/traits_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'implements trait for struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/traits_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'implements trait with arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/traits_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows multiple types to implement same trait' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
