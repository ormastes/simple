# Dual Syntax for Argument Assignment Specification
*Source:* `test/feature/usage/parser_dual_argument_syntax_spec.spl`
**Feature IDs:** #1200-1210  |  **Category:** Syntax  |  **Status:** Implemented

## Overview




## Overview

Support BOTH ':' and '=' for argument assignment in ALL contexts.

## Feature: Dual Syntax - Function Calls

## Function Call Argument Assignment

    Function calls already supported both ':' and '=' - these are regression tests.

### Scenario: colon syntax in function calls

| # | Example | Status |
|---|---------|--------|
| 1 | accepts single named argument with colon | pass |
| 2 | accepts multiple named arguments with colons | pass |

**Example:** accepts single named argument with colon
    Given val result = greet(name: "World")
    Then  expect(result).to_equal("Hello, World!")

**Example:** accepts multiple named arguments with colons
    Given val result = add(a: 10, b: 20)
    Then  expect(result).to_equal(30)

### Scenario: equals syntax in function calls

| # | Example | Status |
|---|---------|--------|
| 1 | accepts single named argument with equals | pass |
| 2 | accepts multiple named arguments with equals | pass |

**Example:** accepts single named argument with equals
    Given val result = greet(name = "World")
    Then  expect(result).to_equal("Hello, World!")

**Example:** accepts multiple named arguments with equals
    Given val result = add(a = 10, b = 20)
    Then  expect(result).to_equal(30)

### Scenario: mixed syntax in function calls

| # | Example | Status |
|---|---------|--------|
| 1 | accepts mixed colon and equals syntax | pass |
| 2 | produces identical results regardless of syntax | pass |

**Example:** accepts mixed colon and equals syntax
    Given val result = compute(a: 10, b = 20, c: 12)
    Then  expect(result).to_equal(250)

**Example:** produces identical results regardless of syntax
    Given val result1 = format_vals(prefix: "[", value: 42, suffix: "]")
    Given val result2 = format_vals(prefix = "[", value = 42, suffix = "]")
    Given val result3 = format_vals(prefix: "[", value = 42, suffix: "]")
    Then  expect(result1).to_equal(result2)
    Then  expect(result2).to_equal(result3)

## Feature: Dual Syntax - Struct Initialization

## Struct Field Assignment

    Struct initialization now supports both ':' and '='.

### Scenario: colon syntax in struct init

| # | Example | Status |
|---|---------|--------|
| 1 | accepts single field with colon | pass |
| 2 | accepts multiple fields with colons | pass |
| 3 | accepts many fields with colons | pass |

**Example:** accepts single field with colon
    Given val person = Person(name: "Alice")
    Then  expect(person.name).to_equal("Alice")

**Example:** accepts multiple fields with colons
    Given val point = Point(x: 3, y: 4)
    Then  expect(point.x).to_equal(3)
    Then  expect(point.y).to_equal(4)

**Example:** accepts many fields with colons
    Given val rect = Rectangle(x: 10, y: 20, width: 100, height: 50)
    Then  expect(rect.width).to_equal(100)
    Then  expect(rect.height).to_equal(50)

### Scenario: equals syntax in struct init

| # | Example | Status |
|---|---------|--------|
| 1 | accepts single field with equals | pass |
| 2 | accepts multiple fields with equals | pass |
| 3 | accepts many fields with equals | pass |

**Example:** accepts single field with equals
    Given val person = Person(name = "Bob")
    Then  expect(person.name).to_equal("Bob")

**Example:** accepts multiple fields with equals
    Given val point = Point(x = 5, y = 6)
    Then  expect(point.x).to_equal(5)
    Then  expect(point.y).to_equal(6)

**Example:** accepts many fields with equals
    Given val rect = Rectangle(x = 0, y = 0, width = 200, height = 100)
    Then  expect(rect.width).to_equal(200)
    Then  expect(rect.height).to_equal(100)

### Scenario: mixed syntax in struct init

| # | Example | Status |
|---|---------|--------|
| 1 | accepts mixed colon and equals syntax | pass |
| 2 | produces identical structs regardless of syntax | pass |

**Example:** accepts mixed colon and equals syntax
    Given val config = Config(host: "localhost", port = 8080, timeout: 30, retries = 3)
    Then  expect(config.host).to_equal("localhost")
    Then  expect(config.port).to_equal(8080)
    Then  expect(config.timeout).to_equal(30)
    Then  expect(config.retries).to_equal(3)

**Example:** produces identical structs regardless of syntax
    Given val p1 = Point(x: 10, y: 20)
    Given val p2 = Point(x = 10, y = 20)
    Given val p3 = Point(x: 10, y = 20)
    Then  expect(p1.x).to_equal(p2.x)
    Then  expect(p1.y).to_equal(p2.y)
    Then  expect(p2.x).to_equal(p3.x)
    Then  expect(p2.y).to_equal(p3.y)

### Scenario: shorthand syntax still works

| # | Example | Status |
|---|---------|--------|
| 1 | accepts shorthand syntax | pass |
| 2 | mixes shorthand with explicit syntax | pass |

**Example:** accepts shorthand syntax
    Given val x = 7
    Given val y = 8
    Given val point = Point(x, y)
    Then  expect(point.x).to_equal(7)
    Then  expect(point.y).to_equal(8)

**Example:** mixes shorthand with explicit syntax
    Given val x = 9
    Given val point = Point(x, y: 10)
    Then  expect(point.x).to_equal(9)
    Then  expect(point.y).to_equal(10)

## Feature: Dual Syntax - No-Paren Calls

## No-Paren Call Argument Assignment

    Skipped because no-paren call argument syntax causes parse issues.

### Scenario: colon syntax in no-paren calls

### Scenario: equals syntax in no-paren calls

### Scenario: mixed syntax in no-paren calls

## Feature: Dual Syntax - Edge Cases

## Edge Cases and Complex Usage

### Scenario: nested calls and struct init

| # | Example | Status |
|---|---------|--------|
| 1 | handles nested function calls with mixed syntax | pass |
| 2 | handles struct init inside function call | pass |
| 3 | handles function call result in struct init | pass |

**Example:** handles nested function calls with mixed syntax
    Given val result = outer(a: inner(x = 5), b = 10)
    Then  expect(result).to_equal(20)

**Example:** handles struct init inside function call
    Given val result = distance(p = Point(x: 3, y: 4))
    Then  expect(result).to_equal(7)

**Example:** handles function call result in struct init
    Given val container = Container(value: get_value())
    Then  expect(container.value).to_equal(42)

### Scenario: multiline arguments

| # | Example | Status |
|---|---------|--------|
| 1 | handles multiline with colon syntax | pass |
| 2 | handles multiline with equals syntax | pass |
| 3 | handles multiline with mixed syntax | pass |

**Example:** handles multiline with colon syntax
    Given val result = long_call(
    Then  expect(result).to_equal(10)

**Example:** handles multiline with equals syntax
    Given val result = long_call(
    Then  expect(result).to_equal(26)

**Example:** handles multiline with mixed syntax
    Given val config = Config(
    Then  expect(config.port).to_equal(443)

### Scenario: whitespace handling

## Feature: Dual Syntax - Consistency

## Syntax Consistency

    Verify that both syntaxes produce identical behavior.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | produces same results in all contexts combined | pass |
| 2 | works identically in real-world scenarios | pass |

**Example:** produces same results in all contexts combined
    Given val r1 = distance(p: Point(x: 10, y: 20))
    Given val r2 = distance(p = Point(x = 10, y = 20))
    Given val r3 = distance(p: Point(x = 10, y = 20))
    Given val r4 = distance(p = Point(x: 10, y = 20))
    Then  expect(r1).to_equal(30)
    Then  expect(r2).to_equal(30)
    Then  expect(r3).to_equal(30)
    Then  expect(r4).to_equal(30)

**Example:** works identically in real-world scenarios
    Given val config1 = Config(server: "localhost", port: 8080, timeout: 30)
    Given val result1 = connect(cfg: config1)
    Given val config2 = Config(server = "localhost", port = 8080, timeout = 30)
    Given val result2 = connect(cfg = config2)
    Given val config3 = Config(server: "localhost", port = 8080, timeout: 30)
    Given val result3 = connect(cfg = config3)
    Then  expect(result1).to_equal("Connected to localhost:8080")
    Then  expect(result2).to_equal("Connected to localhost:8080")
    Then  expect(result3).to_equal("Connected to localhost:8080")


