# Enum Types Specification
*Source:* `test/feature/usage/enums_spec.spl`
**Feature IDs:** #1003  |  **Category:** Language  |  **Status:** Complete

## Overview



use std.text.{NL}

Tests for enumeration types and pattern matching on enums.
Verifies enum definition, construction, and exhaustive pattern matching.

## Feature: Enum Types

Tests for enumeration types and their usage patterns.
    Verifies enum creation, construction, pattern matching, and associated values.

### Scenario: basic enum definition

### Scenario: Simple Enums

        Tests basic enumeration definitions with simple variants.

| # | Example | Status |
|---|---------|--------|
| 1 | defines simple enum with variants | pass |
| 2 | constructs enum variants | pass |
| 3 | matches on enum variants | pass |

**Example:** defines simple enum with variants
    Given val c = Color.Red
    Then  expect(c == Color.Red)

**Example:** constructs enum variants
    Given val s1 = Status.Active
    Given val s2 = Status.Inactive

**Example:** matches on enum variants
    Given val s = ResultType.Success
    Given val result = match s:
    Then  expect(result == "ok")

### Scenario: enums with associated values

### Scenario: Enums with Data

        Tests enums that carry associated data with each variant.

| # | Example | Status |
|---|---------|--------|
| 1 | defines enum with tuple variants | pass |
| 2 | constructs variant with associated values | pass |
| 3 | extracts values from enum variant | pass |
| 4 | matches and binds enum values | pass |

**Example:** defines enum with tuple variants
    Given val circle = Shape.Circle(10)
    Then  expect(circle == Shape.Circle(10))

**Example:** constructs variant with associated values
    Given val msg1 = Message.Text("hello")
    Given val msg2 = Message.Number(42)

**Example:** extracts values from enum variant
    Given val p = Point.Coord(3, 4)
    Then  expect(x == 3)
    Then  expect(y == 4)

**Example:** matches and binds enum values
    Given val r = TestResult.Ok(42)
    Given val value = match r:
    Then  expect(value == 42)

### Scenario: enum pattern matching

### Scenario: Exhaustive Pattern Matching

        Tests pattern matching on enums with exhaustiveness checking.

| # | Example | Status |
|---|---------|--------|
| 1 | requires exhaustive pattern matching | pass |
| 2 | handles all enum variants in match | pass |
| 3 | supports wildcard patterns in match | pass |
| 4 | matches enum in conditional guards | pass |

**Example:** requires exhaustive pattern matching
    Given val c = Color.Red
    Given val name = match c:
    Then  expect(name == "red")

**Example:** handles all enum variants in match
    Given val s = Status.Active
    Given val is_active = match s:
    Then  expect(is_active == true)

**Example:** supports wildcard patterns in match
    Given val c = Color.Green
    Given val is_red = match c:
    Then  expect(is_red == false)

**Example:** matches enum in conditional guards
    Given val s = Status.Active

### Scenario: nested enums

### Scenario: Complex Enum Structures

        Tests enums containing other enums or complex types.

| # | Example | Status |
|---|---------|--------|
| 1 | defines enum with enum variants | pass |
| 2 | matches nested enum variants | pass |
| 3 | handles enum with generic variants | pass |

**Example:** defines enum with enum variants
    Given val msg = Message.Text("test")
    Given val container = Container.Value(msg)
    Then  expect(container == Container.Value(Message.Text("test")))

**Example:** matches nested enum variants
    Given val c = Container.Value(Message.Number(42))
    Given val result = match c:
    Then  expect(result == 42)

**Example:** handles enum with generic variants
    Given val tree = Tree.Node(10, 20)
    Given val sum = match tree:
    Then  expect(sum == 30)

### Scenario: enum methods

### Scenario: Enum Behavior

        Tests methods and behaviors on enumeration types.

| # | Example | Status |
|---|---------|--------|
| 1 | calls methods on enum instances | pass |
| 2 | implements trait for enum | pass |
| 3 | enumerates all variants | pass |

**Example:** calls methods on enum instances
    Given val s = Status.Active

**Example:** implements trait for enum
    Given val c1 = Color.Red
    Given val c2 = Color.Red
    Then  expect(c1 == c2)

**Example:** enumerates all variants
    Given val r = Color.Red
    Given val g = Color.Green
    Given val b = Color.Blue

### Scenario: option and result enums

### Scenario: Built-in Enums

        Tests the built-in Option and Result enumeration types.

| # | Example | Status |
|---|---------|--------|
| 1 | creates Option variants | pass |
| 2 | matches on Option | pass |
| 3 | creates Result variants | pass |
| 4 | matches on Result with error handling | pass |

**Example:** creates Option variants
    Given val some_val = Option.Some(42)
    Given val none_val = Option.None
    Then  expect(some_val == Option.Some(42))

**Example:** matches on Option
    Given val opt = Option.Some(10)
    Given val value = match opt:
    Then  expect(value == 10)

**Example:** creates Result variants
    Given val ok_val = Result.Ok(42)
    Given val err_val = Result.Err("error")
    Then  expect(ok_val == Result.Ok(42))

**Example:** matches on Result with error handling
    Given val res = Result.Ok(100)
    Given val value = match res:
    Then  expect(value == 100)


