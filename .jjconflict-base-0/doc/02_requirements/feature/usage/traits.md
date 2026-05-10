# Traits Specification
*Source:* `test/feature/usage/traits_spec.spl`
**Feature IDs:** #TBD  |  **Category:** Language  |  **Status:** Implemented

## Overview



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

## Feature: Traits

## Core Trait Functionality

    Tests for trait definition, implementation, and usage including
    default methods, trait bounds, and multiple trait implementations.

### Scenario: basic trait implementation

### Scenario: Trait Implementation

        Tests implementing traits for structs.

| # | Example | Status |
|---|---------|--------|
| 1 | implements trait for struct | pass |
| 2 | implements trait with arguments | pass |

**Example:** implements trait for struct
    Given val p = Point { x: 10, y: 20 }
    Then  expect p.sum() == 30

**Example:** implements trait with arguments
    Given val c = Counter { value: 50 }
    Then  expect c.add(25) == 75

### Scenario: multiple trait implementations

### Scenario: Multiple Types Implementing Same Trait

        Tests polymorphism through trait implementations.

| # | Example | Status |
|---|---------|--------|
| 1 | allows multiple types to implement same trait | pass |

**Example:** allows multiple types to implement same trait
    Given val c = Coin { amount: 5 }
    Given val b = Bill { amount: 2 }
    Then  expect c.value() + b.value() == 205

### Scenario: multiple traits on one type

| # | Example | Status |
|---|---------|--------|
| 1 | type implements two different traits | pass |
| 2 | type implements three traits | pass |

**Example:** type implements two different traits
    Given val p = Player { name: "Alice", score: 99 }
    Then  expect p.get_name() == "Alice"
    Then  expect p.get_score() == 99

**Example:** type implements three traits
    Given val t = Task { tid: 1, name: "deploy", prio: 5 }
    Then  expect t.id() == 1
    Then  expect t.label() == "deploy"
    Then  expect t.priority() == 5

## Feature: Default Trait Methods

## Default Method Implementations

    Tests for traits with default method implementations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses default trait method when not overridden | pass |
| 2 | allows overriding default trait method | pass |
| 3 | default method can call abstract method | pass |
| 4 | default method can call other default method | pass |

**Example:** uses default trait method when not overridden
    Given val p = Person { name: "Alice" }
    Then  expect p.farewell() == 99

**Example:** allows overriding default trait method
    Given val p = Person { name: "Bob" }
    Then  expect p.farewell() == 7

**Example:** default method can call abstract method
    Given val v = Value { n: 21 }
    Then  expect v.double() == 42

**Example:** default method can call other default method
    Given val u = Unit { x: 3 }
    Then  expect u.base() == 3
    Then  expect u.step() == 30
    Then  expect u.final_val() == 35

## Feature: Dynamic Trait Objects

## dyn Trait for Dynamic Dispatch

    Tests for trait objects enabling runtime polymorphism.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | coerces concrete type to dyn Trait via let binding | pass |
| 2 | passes concrete type to dyn Trait parameter | pass |
| 3 | handles multiple types via dyn Trait | pass |
| 4 | dyn Trait with default method | pass |

**Example:** coerces concrete type to dyn Trait via let binding
    Given val c = Circle { radius: 7 }
    Given val drawable: dyn Drawable = c
    Then  expect drawable.draw() == 21

**Example:** passes concrete type to dyn Trait parameter
    Given val sq = Square { side: 6 }
    Then  expect process_shape(sq) == 36

**Example:** handles multiple types via dyn Trait
    Given val a = A { x: 5 }
    Given val b = B { y: 7 }
    Then  expect get_value(a) + get_value(b) == 157

**Example:** dyn Trait with default method
    Given val g = Greeter { n: 7 }
    Given val dg: dyn Greetable = g
    Then  expect dg.hello() == 42
    Then  expect dg.custom() == 7

## Feature: Trait and Mixin Integration

## Traits Applied to Classes with Mixins

    Tests that traits work correctly on classes that use mixins.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | trait impl accesses mixin fields | pass |
| 2 | multiple traits on class with mixin | pass |
| 3 | dyn Trait dispatch on mixin class | pass |
| 4 | mixin method and trait method coexist | pass |

**Example:** trait impl accesses mixin fields
    Given val w = Worker(data: 7, factor: 3)
    Then  expect w.compute() == 21

**Example:** multiple traits on class with mixin
    Given val h = Hero(id: 1, name: "Zara", power: 95)
    Then  expect h.get_label() == "Zara #1"
    Then  expect h.get_rank() == 95

**Example:** dyn Trait dispatch on mixin class
    Given val r = Rect(width: 5, height: 8)
    Then  expect get_measure(r) == 40

**Example:** mixin method and trait method coexist
    Given val e = Entry(score: 88, label: "gold")
    Then  expect e.get_score() == 88
    Then  expect e.tag() == "gold"


