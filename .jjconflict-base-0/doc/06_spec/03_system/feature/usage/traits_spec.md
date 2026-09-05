# Traits Specification

> Traits define shared behavior that types can implement, enabling polymorphism and code reuse. They are similar to interfaces in other languages but support default implementations, associated types, and trait bounds for generics.

<!-- sdn-diagram:id=traits_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=traits_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

traits_spec -> HasData
traits_spec -> Identified
traits_spec -> Sized
traits_spec -> Scored
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=traits_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/traits_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Traits define shared behavior that types can implement, enabling polymorphism
and code reuse. They are similar to interfaces in other languages but support
default implementations, associated types, and trait bounds for generics.

## Syntax

```simple
trait Printable:
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

1. fn sum
2. fn sum
3. expect p sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn add
2. fn add
3. expect c add


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn value
2. fn value
3. fn value
4. expect c value


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn get name
2. fn get score
3. fn get name
4. fn get score
5. expect p get name
6. expect p get score


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn id
2. fn label
3. fn priority
4. fn id
5. fn label
6. fn priority
7. expect t id
8. expect t label
9. expect t priority


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn greet
2. fn farewell
3. fn greet
4. expect p farewell


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn greet
2. fn farewell
3. fn greet
4. fn farewell
5. expect p farewell


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn compute
2. fn double
3. fn compute
4. expect v double


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn base
2. fn step
3. fn final val
4. fn base
5. expect u base
6. expect u step
7. expect u final val


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn draw
2. fn draw
3. expect drawable draw


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn area
2. fn area
3. fn process shape
4. expect process shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn value
2. fn value
3. fn value
4. fn get value
5. expect get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn hello
2. fn custom
3. fn custom
4. expect dg hello
5. expect dg custom


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn compute
2. fn compute
3. expect w compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn get label
2. fn get rank
3. fn get label
4. fn get rank
5. expect h get label
6. expect h get rank


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn measure
2. fn measure
3. fn get measure
4. expect get measure


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn tag
2. fn get score
3. fn tag
4. expect e get score
5. expect e tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
