# Classes and Object-Oriented Programming Specification
*Source:* `test/feature/usage/classes_spec.spl`
**Feature IDs:** #OOP-001  |  **Category:** Language | Classes  |  **Status:** Implemented

## Overview



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

## Feature: Static Class Methods

## Static Method Definitions

    Tests for static methods on classes using `static fn`.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | calls static method on class | pass |
| 2 | calls multiple static methods | pass |

**Example:** calls static method on class
    Then  expect Calculator.add(3, 4) == 7

**Example:** calls multiple static methods
    Then  expect Math.double(5) + Math.triple(4) == 22

## Feature: Impl Blocks

## Implementation Blocks for Structs

    Tests for adding methods to structs via impl blocks.
    Note: Block-scoped impl blocks are not yet supported. These tests
    are skipped but verified via Rust tests in interpreter_oop.rs.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | adds method to struct via impl | pass |
| 2 | adds method with arguments via impl | pass |

**Example:** adds method to struct via impl
    Given val p = Point { x: 15, y: 25 }
    Then  expect p.sum() == 40

**Example:** adds method with arguments via impl
    Given val c = Counter { value: 10 }
    Then  expect c.add(5) == 15

## Feature: Class Instantiation

## Direct Construction Syntax

    Tests for creating class instances with ClassName(field: value).

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates instances with direct construction | pass |
| 2 | accesses string field | pass |
| 3 | creates class with default field values | pass |

**Example:** creates instances with direct construction
    Given val p = Person { name: "Alice", age: 30 }
    Then  expect p.age == 30

**Example:** accesses string field
    Given val g = Greeting { message: "Hello" }
    Given var result = 0
    Then  expect result == 1

**Example:** creates class with default field values
    Given val c = Counter {}
    Then  expect c.count == 0

## Feature: Instance Methods

## Methods Defined in Class Body

    Tests for instance methods with self access.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | calls instance method | pass |
| 2 | calls method with arguments | pass |

**Example:** calls instance method
    Given val b = Box { value: 21 }
    Then  expect b.get_double() == 42

**Example:** calls method with arguments
    Given val a = Adder { base: 10 }
    Then  expect a.add(5) == 15

## Feature: Context Blocks

## Context Block for Method Dispatch

    Tests for `context obj:` blocks where unqualified calls dispatch to context object.
    Note: Block-scoped context blocks are not yet supported. These tests
    are skipped but verified via Rust tests in interpreter_oop.rs.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | dispatches method to context object | pass |
| 2 | accesses self fields in context method | pass |

**Example:** dispatches method to context object
    Given val calc = Calculator {}
    Given var res = 0
    Then  expect res == 42

**Example:** accesses self fields in context method
    Given val a = Adder { base: 30 }
    Given var res = 0
    Then  expect res == 42

## Feature: Method Missing

## Dynamic Method Dispatch via method_missing

    Tests for method_missing which handles calls to undefined methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | calls method_missing for unknown method | pass |
| 2 | passes arguments to method_missing | pass |
| 3 | uses method_missing in context block | pass |

**Example:** calls method_missing for unknown method
    Given val d = DSL {}
    Then  expect d.unknown_method() == 42

**Example:** passes arguments to method_missing
    Given val x = args[0]
    Given val m = Multiplier { factor: 7 }
    Then  expect m.any_method(6) == 42

**Example:** uses method_missing in context block
    Given val c = Counter { count: 0 }
    Given var res = 0
    Then  expect res == 42

## Feature: Auto-Forwarding Properties

## Property Getter/Setter Patterns

    Tests for get_/set_/is_ method patterns with backing _field.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | gets property via get_ method | pass |
| 2 | sets property via set_ method returning new instance | pass |
| 3 | checks boolean property via is_ method | pass |
| 4 | uses combined getter and setter | pass |

**Example:** gets property via get_ method
    Given val p = Person { _name: "Alice" }
    Given var result = 0
    Then  expect result == 1

**Example:** sets property via set_ method returning new instance
    Given val c = Counter { _value: 10 }
    Given val c2 = c.set_value(42)
    Then  expect c2.get_value() == 42

**Example:** checks boolean property via is_ method
    Given val item = Item { _active: true }
    Given var result = 0
    Then  expect result == 1

**Example:** uses combined getter and setter
    Given val b = Box { _content: 0 }
    Given val b2 = b.set_content(100)
    Then  expect b2.get_content() == 100

## Feature: Static Polymorphism

## Interface Bindings with bind Statement

    Tests for static polymorphism where trait bindings enable
    compile-time dispatch to concrete implementations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | binds trait to concrete class | pass |
| 2 | binds trait with multiple methods | pass |
| 3 | binds trait with fields | pass |
| 4 | passes bound trait as function parameter | pass |

**Example:** binds trait to concrete class
    Given val logger: Logger = create_logger()
    Given val res = logger.log("Hello")
    Given var result = 0
    Then  expect result == 1

**Example:** binds trait with multiple methods
    Given val calc: Calculator = SimpleCalc {}
    Then  expect calc.add(3, 4) + calc.multiply(2, 5) == 17

**Example:** binds trait with fields
    Given val counter: Counter = SimpleCounter { value: 42 }
    Then  expect counter.get_value() == 42

**Example:** passes bound trait as function parameter
    Given val greeter: Greeter = FormalGreeter { multiplier: 5 }
    Then  expect do_greeting(greeter) == 50

## Feature: Trait Polymorphism

## Multiple Types Implementing Same Trait

    Tests for polymorphism through trait implementations.
    Note: Block-scoped trait implementations are not yet supported.
    This test is skipped but verified via Rust tests in interpreter_oop.rs.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | calculates different areas via Shape trait | pass |

**Example:** calculates different areas via Shape trait
    Given val s = Square { side: 5 }
    Given val r = Rectangle { width: 4, height: 3 }
    Then  expect s.area() + r.area() == 37


