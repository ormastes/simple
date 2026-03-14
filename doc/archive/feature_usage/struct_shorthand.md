# Struct Field Shorthand Specification
*Source:* `test/feature/usage/struct_shorthand_spec.spl`
**Feature IDs:** #STRUCT-SHORTHAND  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



Struct field shorthand allows omitting the field name when the variable name
matches. This reduces boilerplate when constructing structs from local variables.

## Syntax

```simple
# Without shorthand (verbose)
val point = Point(x: x, y: y)

# With shorthand (when variable names match field names)
val point = Point(x, y)

# Mixed shorthand and explicit
val point = Point(x, y: computed_y)
```

## Key Behaviors

- Variable name must exactly match the field name
- Order must match the struct definition
- Can mix shorthand and explicit field names
- Works with any struct type

## Feature: Struct Field Shorthand

## Struct Construction Shorthand Specification

    Struct shorthand syntax reduces verbosity when constructing structs from
    variables with matching names. This test suite verifies:
    - Basic shorthand when variable matches field name
    - Mixed shorthand and explicit field syntax
    - Shorthand with different field types
    - Interaction with nested structs
    - Error cases (mismatched names still require explicit syntax)

### Scenario: basic struct shorthand

| # | Example | Status |
|---|---------|--------|
| 1 | uses shorthand for matching variable names | pass |
| 2 | constructs struct with all shorthand fields | pass |

**Example:** uses shorthand for matching variable names
    Given val x = 10
    Given val y = 20
    Given val point = Point(x, y)
    Then  expect point.x == 10
    Then  expect point.y == 20

**Example:** constructs struct with all shorthand fields
    Given val name = "Alice"
    Given val age = 30
    Given val person = Person(name, age)
    Then  expect person.name == "Alice"
    Then  expect person.age == 30

### Scenario: mixed shorthand and explicit

| # | Example | Status |
|---|---------|--------|
| 1 | mixes shorthand with explicit named argument | pass |
| 2 | uses explicit then shorthand | pass |
| 3 | mixes in complex struct | pass |

**Example:** mixes shorthand with explicit named argument
    Given val x = 10
    Given val point = Point(x, y: 20)
    Then  expect point.x == 10
    Then  expect point.y == 20

**Example:** uses explicit then shorthand
    Given val y = 20
    Given val point = Point(x: 10, y)
    Then  expect point.x == 10
    Then  expect point.y == 20

**Example:** mixes in complex struct
    Given val host = "localhost"
    Given val timeout = 30
    Given val config = Config(host, port: 8080, timeout)
    Then  expect config.host == "localhost"
    Then  expect config.port == 8080
    Then  expect config.timeout == 30

### Scenario: shorthand with computed values

| # | Example | Status |
|---|---------|--------|
| 1 | uses shorthand after computation | pass |
| 2 | uses shorthand from function return | pass |

**Example:** uses shorthand after computation
    Given val width = 5 * 2
    Given val height = 3 * 2
    Given val rect = Rectangle(width, height)
    Then  expect rect.width == 10
    Then  expect rect.height == 6

**Example:** uses shorthand from function return
    Given val x = get_x()
    Given val y = get_y()
    Given val point = Point(x, y)
    Then  expect point.x == 100
    Then  expect point.y == 200

### Scenario: shorthand with different types

| # | Example | Status |
|---|---------|--------|
| 1 | handles text fields | pass |
| 2 | handles boolean fields | pass |
| 3 | handles mixed types | pass |

**Example:** handles text fields
    Given val sender = "Alice"
    Given val content = "Hello!"
    Given val msg = Message(sender, content)
    Then  expect msg.sender == "Alice"
    Then  expect msg.content == "Hello!"

**Example:** handles boolean fields
    Given val enabled = true
    Given val visible = false
    Given val flags = Flags(enabled, visible)
    Then  expect flags.enabled == true
    Then  expect flags.visible == false

**Example:** handles mixed types
    Given val id = 42
    Given val name = "Test"
    Given val active = true
    Given val record = Record(id, name, active)
    Then  expect record.id == 42
    Then  expect record.name == "Test"
    Then  expect record.active == true

### Scenario: shorthand in nested structs

| # | Example | Status |
|---|---------|--------|
| 1 | uses shorthand when nesting | pass |

**Example:** uses shorthand when nesting
    Given val x = 0
    Given val y = 0
    Given val start = Point(x, y)
    Given val x2 = 10
    Given val y2 = 10
    Given val endpoint = Point(x: x2, y: y2)
    Given val line = Line(start, endpoint)
    Then  expect line.start.x == 0
    Then  expect line.endpoint.x == 10

### Scenario: explicit syntax still works

| # | Example | Status |
|---|---------|--------|
| 1 | allows fully explicit construction | pass |
| 2 | allows equals syntax explicitly | pass |

**Example:** allows fully explicit construction
    Given val a = 100
    Given val b = 200
    Given val point = Point(x: a, y: b)
    Then  expect point.x == 100
    Then  expect point.y == 200

**Example:** allows equals syntax explicitly
    Given val point = Point(x=30, y=40)
    Then  expect point.x == 30
    Then  expect point.y == 40

### Scenario: shorthand in collections

| # | Example | Status |
|---|---------|--------|
| 1 | uses shorthand in list of structs | pass |
| 2 | uses shorthand with map | pass |

**Example:** uses shorthand in list of structs
    Given var points: [Point] = []
    Given val x = i * 10
    Given val y = i * 20
    Then  expect points[0].x == 0
    Then  expect points[1].x == 10
    Then  expect points[2].x == 20

**Example:** uses shorthand with map
    Given val coords = [(1, 2), (3, 4), (5, 6)]
    Given val points = coords.map(\pair:
    Given val (x, y) = pair
    Then  expect points[0].x == 1
    Then  expect points[1].y == 4


