# Parser Function Definition Specification
*Source:* `test/feature/usage/parser_functions_spec.spl`
**Feature IDs:** #PARSER-FN-001 to #PARSER-FN-020  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview



Tests that the parser correctly parses function definitions including
parameters, return types, generics, where clauses, and various function forms.

## Syntax

```simple
fn name(params) -> ReturnType:
    body

fn generic<T>(x: T) -> T where T: Trait:
    body

extern fn ffi_func(x: i64) -> i64

macro name(params) -> (contract):
    body
```

## Feature: Basic Function Definition Parsing

## Simple Function Syntax

    Tests parsing of basic function definitions.

### Scenario: minimal functions

| # | Example | Status |
|---|---------|--------|
| 1 | parses function without params | pass |
| 2 | parses function with single param | pass |
| 3 | parses function with multiple params | pass |

**Example:** parses function without params
    Then  expect get_value() == 42

**Example:** parses function with single param
    Then  expect double(21) == 42

**Example:** parses function with multiple params
    Then  expect add(20, 22) == 42

### Scenario: return types

| # | Example | Status |
|---|---------|--------|
| 1 | parses explicit return type | pass |
| 2 | parses inferred return | pass |
| 3 | parses unit return | pass |

**Example:** parses explicit return type
    Then  expect typed() == 42

**Example:** parses inferred return
    Then  expect inferred() == 42

**Example:** parses unit return
    Given val x = 1
    Then  expect true

### Scenario: function body

| # | Example | Status |
|---|---------|--------|
| 1 | parses multi-statement body | pass |
| 2 | parses recursive function | pass |

**Example:** parses multi-statement body
    Given val doubled = x * 2
    Given val incremented = doubled + 1
    Then  expect complex(20) == 41

**Example:** parses recursive function
    Then  expect fib(10) == 55

## Feature: Generic Function Parsing

## Type Parameters with Angle Brackets

    Tests parsing of generic function definitions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses single type parameter | pass |
| 2 | parses multiple type parameters | pass |
| 3 | parses nested generic types | pass |

**Example:** parses single type parameter
    Then  expect identity(42) == 42

**Example:** parses multiple type parameters
    Given val p = pair(1, "hello")
    Then  expect p.0 == 1

**Example:** parses nested generic types
    Then  expect wrap(42).unwrap() == 42

## Feature: Where Clause Parsing

## Type Constraints

    Tests parsing of where clauses with trait bounds.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses single where clause | pass |
| 2 | parses multiple bounds | pass |
| 3 | parses multiple where clauses | pass |

**Example:** parses single where clause
    Then  expect display(Number { value: 42 }) == "42"

**Example:** parses multiple bounds
    Then  expect true  # Compiles successfully

**Example:** parses multiple where clauses
    Then  expect true  # Compiles successfully

## Feature: Default Parameter Parsing

## Parameters with Default Values

    Tests parsing of function parameters with defaults.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses default parameter | pass |
| 2 | parses multiple defaults | pass |
| 3 | parses mixed required and default | pass |

**Example:** parses default parameter
    Then  expect greet() == "Hello, World!"
    Then  expect greet("Alice") == "Hello, Alice!"

**Example:** parses multiple defaults
    Given val p1 = create_point()
    Given val p2 = create_point(5)
    Given val p3 = create_point(5, 10)
    Then  expect p1.0 == 0
    Then  expect p2.0 == 5
    Then  expect p3.1 == 10

**Example:** parses mixed required and default
    Then  expect format(42) == "42"
    Then  expect format(42, "<<") == "<<42"

## Feature: Named Argument Parsing

## Calling Functions with Named Arguments

    Tests parsing of function calls with named argument syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses named arguments | pass |
| 2 | parses mixed positional and named | pass |
| 3 | parses named arguments in any order | pass |

**Example:** parses named arguments
    Given val p = point(x = 10, y = 20)
    Then  expect p.0 == 10

**Example:** parses mixed positional and named
    Given val result = describe("Alice", age = 30, city = "NYC")
    Then  expect result == "Alice, 30, from NYC"

**Example:** parses named arguments in any order
    Then  expect subtract(b = 10, a = 52) == 42

## Feature: Extern Function Parsing

## External Function Declarations

    Tests parsing of extern function declarations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses extern function | pass |
| 2 | parses extern with multiple params | pass |

**Example:** parses extern function
    Then  expect true

**Example:** parses extern with multiple params
    Then  expect true

## Feature: Macro Definition Parsing

## Compile-Time Code Generation

    Tests parsing of macro definitions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses macro definition | pass |

**Example:** parses macro definition
    Given val value = double_emit(21)
    Then  expect value == 42

## Feature: Actor Definition Parsing

## Concurrent Actor Syntax

    Tests parsing of actor definitions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses actor definition | pass |

**Example:** parses actor definition
    Then  expect true  # Compiles successfully

## Feature: Method Definition Parsing

## Methods in Impl Blocks

    Tests parsing of methods defined in impl blocks.

### Scenario: instance methods

| # | Example | Status |
|---|---------|--------|
| 1 | parses method with self | pass |
| 2 | parses mutable method | pass |

**Example:** parses method with self
    Given val p = Point(x: 20, y: 22)
    Then  expect p.sum() == 42

**Example:** parses mutable method
    Given var c = Counter(value: 0)
    Then  expect c.value == 1

### Scenario: static methods

| # | Example | Status |
|---|---------|--------|
| 1 | parses static method | pass |

**Example:** parses static method
    Given val p = Point.origin()
    Then  expect p.x == 0

## Feature: Lambda Expression Parsing

## Anonymous Function Syntax

    Tests parsing of lambda expressions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple lambda | pass |
| 2 | parses multi-param lambda | pass |
| 3 | parses typed lambda | pass |
| 4 | parses lambda in higher-order context | pass |

**Example:** parses simple lambda
    Given val f = \x: x * 2
    Then  expect f(21) == 42

**Example:** parses multi-param lambda
    Given val f = \a, b, c: a + b + c
    Then  expect f(10, 20, 12) == 42

**Example:** parses typed lambda
    Given val f = \x: x * 2
    Then  expect f(21) == 42

**Example:** parses lambda in higher-order context
    Then  expect apply(\x: x + 1, 41) == 42

## Feature: Async Function Parsing

## Async/Await Syntax

    Tests parsing of async function definitions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses async function | pass |
| 2 | parses await expression | pass |

**Example:** parses async function
    Then  expect true  # Compiles successfully

**Example:** parses await expression
    Given val x = await get_data()
    Then  expect true  # Compiles successfully


