# Named Argument with Equals Syntax Specification
*Source:* `test/feature/usage/named_arg_equals_spec.spl`
**Feature IDs:** #NAMED-ARG-EQUALS  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



use std.text.{NL}

Named arguments allow passing function arguments by name rather than position.
Simple supports both colon syntax `name: value` and equals syntax `name=value`
for named arguments, providing flexibility in coding style.

## Syntax

```simple
# Colon syntax (preferred for readability)
connect(host: "localhost", port: 8080)

# Equals syntax (concise, especially for single args)
Point(x=3, y=4)

# Mixed with positional
greet("Hello", name="World")
```

## Key Behaviors

- Named arguments can appear in any order
- Named arguments can be mixed with positional arguments
- Positional arguments must come before named arguments
- Both `name: value` and `name=value` syntax are supported

## Feature: Named Arguments with Equals Syntax

## Named Argument Specification

    Named arguments provide explicit parameter binding by name, improving
    code readability and allowing flexible argument ordering. This test
    suite verifies:
    - Basic named argument syntax with `=` and `:`
    - Mixing positional and named arguments
    - Arbitrary ordering of named arguments
    - Named arguments with default parameter values
    - Named arguments in struct construction

### Scenario: basic named arguments with equals

| # | Example | Status |
|---|---------|--------|
| 1 | passes single named argument | pass |
| 2 | passes multiple named arguments | pass |
| 3 | allows reordered named arguments | pass |

**Example:** passes single named argument
    Then  expect greet(name="World") == "Hello, World!"

**Example:** passes multiple named arguments
    Then  expect format_point(x=3, y=4) == "(3, 4)"

**Example:** allows reordered named arguments
    Then  expect format_point(y=4, x=3) == "(3, 4)"

### Scenario: basic named arguments with colon

| # | Example | Status |
|---|---------|--------|
| 1 | passes single named argument with colon | pass |
| 2 | passes multiple named arguments with colon | pass |
| 3 | allows reordered named arguments with colon | pass |

**Example:** passes single named argument with colon
    Then  expect greet(name: "World") == "Hello, World!"

**Example:** passes multiple named arguments with colon
    Then  expect format_point(x: 3, y: 4) == "(3, 4)"

**Example:** allows reordered named arguments with colon
    Then  expect format_point(y: 4, x: 3) == "(3, 4)"

### Scenario: mixed positional and named arguments

| # | Example | Status |
|---|---------|--------|
| 1 | combines positional with named equals | pass |
| 2 | combines positional with named colon | pass |
| 3 | uses multiple positional then named | pass |

**Example:** combines positional with named equals
    Then  expect connect("localhost", port=8080) == "localhost:8080"

**Example:** combines positional with named colon
    Then  expect connect("localhost", port: 8080) == "localhost:8080"

**Example:** uses multiple positional then named
    Then  expect format_record(1, "Alice", active=true) == "1: Alice (active=true)"

### Scenario: named arguments with default values

| # | Example | Status |
|---|---------|--------|
| 1 | uses default when named arg omitted | pass |
| 2 | overrides default with named arg | pass |
| 3 | overrides multiple defaults | pass |
| 4 | overrides defaults in any order | pass |

**Example:** uses default when named arg omitted
    Then  expect create_config(host="example.com") == "example.com:80 (timeout=30)"

**Example:** overrides default with named arg
    Then  expect create_config(host="example.com", port=443) == "example.com:443 (timeout=30)"

**Example:** overrides multiple defaults
    Then  expect create_config(host="example.com", port=443, timeout=60) == "example.com:443 (timeout=60)"

**Example:** overrides defaults in any order
    Then  expect create_config(host="example.com", timeout=120, port=8080) == "example.com:8080 (timeout=120)"

### Scenario: struct construction with named arguments

| # | Example | Status |
|---|---------|--------|
| 1 | constructs struct with equals syntax | pass |
| 2 | constructs struct with colon syntax | pass |
| 3 | allows reordered struct fields | pass |
| 4 | constructs complex struct | pass |

**Example:** constructs struct with equals syntax
    Given val p = Point(x=10, y=20)
    Then  expect p.x == 10
    Then  expect p.y == 20

**Example:** constructs struct with colon syntax
    Given val p = Point(x: 10, y: 20)
    Then  expect p.x == 10
    Then  expect p.y == 20

**Example:** allows reordered struct fields
    Given val p = Point(y=20, x=10)
    Then  expect p.x == 10
    Then  expect p.y == 20

**Example:** constructs complex struct
    Given val person = Person(name="Alice", age=30, active=true)
    Then  expect person.name == "Alice"
    Then  expect person.age == 30
    Then  expect person.active == true

### Scenario: edge cases

| # | Example | Status |
|---|---------|--------|
| 1 | handles single character parameter names | pass |
| 2 | handles longer parameter names | pass |
| 3 | handles underscored parameter names | pass |

**Example:** handles single character parameter names
    Then  expect f(a=1, b=2) == 3

**Example:** handles longer parameter names
    Then  expect calculate(first_operand=5, second_operand=6) == 30

**Example:** handles underscored parameter names
    Then  expect process(input_value=10, max_retries=3) == 30


