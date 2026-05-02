# Implementation Blocks Specification
*Source:* `test/feature/usage/impl_blocks_spec.spl`
**Feature IDs:** #830-835  |  **Category:** Language  |  **Status:** Implemented

## Overview



## Overview

Implementation blocks (`impl`) provide a flexible way to define methods for types outside
of the type definition. This enables separation of concerns, method organization, and
extension of types in different modules without modifying the original definition.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Impl Block | Collection of methods for a type |
| Instance Method | Methods that receive self as implicit parameter |
| Static Method | Methods that don't receive self |
| Method Organization | Grouping related behavior in impl blocks |

## Behavior

- Methods in impl blocks are part of the type's interface
- Impl blocks can be placed in any module or location
- Multiple impl blocks for the same type are merged
- Static methods are called with type name prefix
- Instance methods use dot notation on values

## Feature: Implementation Blocks - Basic

## Basic Impl Block Definition and Usage

    Tests basic implementation block syntax and method definition.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | defines methods in impl block | pass |
| 2 | defines multiple methods | pass |

**Example:** defines methods in impl block
    Given val p = Point(x: 5, y: 10)
    Then  expect p.get_x() == 5

**Example:** defines multiple methods
    Given val r = Rectangle(width: 4, height: 5)
    Then  expect r.area() == 20
    Then  expect r.perimeter() == 18

## Feature: Implementation Blocks - Static Methods

## Static Method Definition

    Tests static methods in implementation blocks.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses static factory method | pass |

**Example:** uses static factory method
    Given val p1 = Point.origin()
    Then  expect p1.x == 0
    Then  expect p1.y == 0
    Given val p2 = Point.from_coords(3, 4)
    Then  expect p2.x == 3
    Then  expect p2.y == 4

## Feature: Implementation Blocks - Instance Methods

## Instance Method Definition

    Tests instance methods that operate on self.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | defines immutable methods | pass |
| 2 | defines mutable methods | pass |

**Example:** defines immutable methods
    Given val c = Circle(radius: 5.0)
    Then  expect c.area() > 78.0
    Then  expect c.circumference() > 31.0

**Example:** defines mutable methods
    Given val c = Counter(count: 0)
    Then  expect c.count == 1
    Then  expect c.count == 0

## Feature: Implementation Blocks - Mixed Methods

## Mixed Method Types

    Impl blocks can contain both static and instance methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | mixes static and instance methods | pass |

**Example:** mixes static and instance methods
    Given val t = Temperature.from_fahrenheit(32.0)
    Then  expect t.celsius > -1.0
    Then  expect t.celsius < 1.0


