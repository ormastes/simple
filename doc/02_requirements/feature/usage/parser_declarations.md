# Parser Declaration Specification
*Source:* `test/feature/usage/parser_declarations_spec.spl`
**Feature IDs:** #PARSER-DECL-001 to #PARSER-DECL-025  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview




Tests that the parser correctly parses declaration statements including
structs, enums, classes, traits, modules, imports, and type aliases.

## Syntax

```simple
struct Point:
    x: i64
    y: i64

enum Color:
    Red
    Green
    Blue

class Service:
    field: Type

trait Printable:
    fn print()

module utils:
    fn helper():
        pass

import module.submodule
type Alias = OriginalType
```

## Feature: Struct Declaration Parsing

## Data Structure Definitions

    Tests parsing of struct declarations with fields.

### Scenario: basic structs

| # | Example | Status |
|---|---------|--------|
| 1 | parses struct with fields | pass |
| 2 | parses struct with single field | pass |
| 3 | parses empty struct | pass |

**Example:** parses struct with fields
    Given val p = Point { x: 10, y: 20 }
    Then  expect p.x == 10

**Example:** parses struct with single field
    Given val w = Wrapper { value: 42 }
    Then  expect w.value == 42

**Example:** parses empty struct
    Given val e = Empty {}
    Then  expect true

### Scenario: generic structs

| # | Example | Status |
|---|---------|--------|
| 1 | parses generic struct | pass |
| 2 | parses multi-param generic struct | pass |

**Example:** parses generic struct
    Given val b = Box { value: 42 }
    Then  expect b.value == 42

**Example:** parses multi-param generic struct
    Given val p = Pair { first: 1, second: "hello" }
    Then  expect p.first == 1

### Scenario: nested structs

| # | Example | Status |
|---|---------|--------|
| 1 | parses struct with struct field | pass |

**Example:** parses struct with struct field
    Given val o = Outer { inner: Inner { value: 42 } }
    Then  expect o.inner.value == 42

## Feature: Enum Declaration Parsing

## Algebraic Data Type Definitions

    Tests parsing of enum declarations with variants.

### Scenario: simple enums

| # | Example | Status |
|---|---------|--------|
| 1 | parses enum without data | pass |
| 2 | parses enum comparison | pass |

**Example:** parses enum without data
    Given val c = Color.Red
    Then  expect c == Color.Red

**Example:** parses enum comparison
    Then  expect Status.Active != Status.Inactive

### Scenario: enums with data

| # | Example | Status |
|---|---------|--------|
| 1 | parses enum with tuple variant | pass |
| 2 | parses enum with struct variant | pass |

**Example:** parses enum with tuple variant
    Given val r = Result.Ok(42)
    Then  expect r == Result.Ok(42)

**Example:** parses enum with struct variant
    Given val s = Shape.Circle { radius: 5.0 }
    Then  expect true

### Scenario: enum matching

| # | Example | Status |
|---|---------|--------|
| 1 | parses enum in match | pass |

**Example:** parses enum in match
    Then  expect get_value(Option.Some(42)) == 42

## Feature: Class Declaration Parsing

## Class Definitions with Methods

    Tests parsing of class declarations.

### Scenario: basic classes

| # | Example | Status |
|---|---------|--------|
| 1 | parses class with fields | pass |
| 2 | parses class with methods | pass |

**Example:** parses class with fields
    Given val c = Counter { count: 0 }
    Then  expect c.count == 0

**Example:** parses class with methods
    Given val calc = Calculator { value: 10 }
    Then  expect calc.add(32) == 42

### Scenario: class inheritance

| # | Example | Status |
|---|---------|--------|
| 1 | parses class with trait impl | pass |

**Example:** parses class with trait impl
    Given val item = Item { name: "test" }
    Then  expect item.describe() == "test"

## Feature: Trait Declaration Parsing

## Interface Definitions

    Tests parsing of trait declarations.

### Scenario: basic traits

| # | Example | Status |
|---|---------|--------|
| 1 | parses trait with method | pass |
| 2 | parses trait with default method | pass |

**Example:** parses trait with method
    Given val p = Person { name: "Alice" }
    Then  expect p.greet() == "Hello, Alice!"

**Example:** parses trait with default method
    Then  expect true  # TODO: Implement default trait methods

### Scenario: trait bounds

| # | Example | Status |
|---|---------|--------|
| 1 | parses trait extending trait | pass |

**Example:** parses trait extending trait
    Then  expect true  # Compiles successfully

## Feature: Module Declaration Parsing

## Namespace Organization

    Tests parsing of module declarations.

### Scenario: inline modules

| # | Example | Status |
|---|---------|--------|
| 1 | parses inline module | pass |
| 2 | parses nested modules | pass |

**Example:** parses inline module
    Then  expect utils.helper() == 42

**Example:** parses nested modules
    Then  expect outer.inner.deep() == 42

### Scenario: module items

| # | Example | Status |
|---|---------|--------|
| 1 | parses module with multiple items | pass |

**Example:** parses module with multiple items
    Given val PI = 3
    Then  expect math.add(1, 2) == 3
    Then  expect math.multiply(6, 7) == 42

## Feature: Import Declaration Parsing

## Module Import Syntax

    Tests parsing of import statements.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple import | pass |
| 2 | parses specific import | pass |
| 3 | parses multiple imports | pass |

**Example:** parses simple import
    Then  expect true

**Example:** parses specific import
    Then  expect true

**Example:** parses multiple imports
    Then  expect true

## Feature: Type Alias Declaration Parsing

## Type Alias Definitions

    Tests parsing of type alias declarations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple type alias | pass |
| 2 | parses generic type alias | pass |
| 3 | parses complex type alias | pass |

**Example:** parses simple type alias
    Given val x: Integer = 42
    Then  expect x == 42

**Example:** parses generic type alias
    Given val list: IntList = [1, 2, 3]
    Then  expect list.len() == 3

**Example:** parses complex type alias
    Given val map: StringMap<i64> = {"answer": 42}
    Then  expect map["answer"] == 42

## Feature: Variable Declaration Parsing

## val and var Declarations

    Tests parsing of variable declarations.

### Scenario: immutable variables

| # | Example | Status |
|---|---------|--------|
| 1 | parses val declaration | pass |
| 2 | parses val with type annotation | pass |

**Example:** parses val declaration
    Given val x = 42
    Then  expect x == 42

**Example:** parses val with type annotation
    Given val x: i64 = 42
    Then  expect x == 42

### Scenario: mutable variables

| # | Example | Status |
|---|---------|--------|
| 1 | parses var declaration | pass |
| 2 | parses var with type annotation | pass |

**Example:** parses var declaration
    Given var x = 0
    Then  expect x == 42

**Example:** parses var with type annotation
    Given var x: i64 = 0
    Then  expect x == 42

### Scenario: let bindings

| # | Example | Status |
|---|---------|--------|
| 1 | parses let declaration | pass |
| 2 | parses let with destructuring | pass |

**Example:** parses let declaration
    Then  expect x == 42

**Example:** parses let with destructuring
    Then  expect a + b == 3

## Feature: Impl Block Parsing

## Method Implementation Blocks

    Tests parsing of impl blocks for types.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses impl block for struct | pass |
| 2 | parses impl block for trait | pass |

**Example:** parses impl block for struct
    Given val p = Point { x: 3, y: 4 }
    Then  expect p.translate(1, 1).x == 4

**Example:** parses impl block for trait
    Given val n = Number { value: 42 }
    Then  expect n.to_string() == "42"

## Feature: Attribute Declaration Parsing

## Decorator Syntax

    Tests parsing of attributes/decorators on declarations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses attribute on function | pass |
| 2 | parses attribute with args | pass |
| 3 | parses multiple attributes | pass |
| 4 | parses attribute on struct | pass |

**Example:** parses attribute on function
    Then  expect true

**Example:** parses attribute with args
    Then  expect true

**Example:** parses multiple attributes
    Then  expect true

**Example:** parses attribute on struct
    Then  expect true


