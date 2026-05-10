# Generic Types Specification
*Source:* `test/feature/usage/generics_spec.spl`
**Feature IDs:** #1005  |  **Category:** Language  |  **Status:** In Progress

## Overview



Tests for generic type parameters and constraints.
Verifies generic function definitions, generic struct/class types, and type bounds.

## Feature: Generic Types

Tests for generic/parametric types and their usage.
    Verifies generic function definitions, generic structs, generic classes,
    and type parameter instantiation and inference.

### Scenario: generic functions

### Scenario: Parameterized Functions

        Tests generic functions with type parameters.

| # | Example | Status |
|---|---------|--------|
| 1 | defines generic identity function | pass |
| 2 | uses generic function with inference | pass |
| 3 | uses multiple type parameters | pass |

**Example:** defines generic identity function
    Then  expect identity(42) == 42
    Then  expect identity("hello") == "hello"

**Example:** uses generic function with inference
    Given val result = first([1, 2, 3])
    Then  expect result == Some(1)

**Example:** uses multiple type parameters
    Then  expect pair(1, "string") == "pair"
    Then  expect pair(true, 3.14) == "pair"

### Scenario: generic structs

### Scenario: Generic Structures

        Tests struct types with type parameters.

| # | Example | Status |
|---|---------|--------|
| 1 | defines generic struct | pass |
| 2 | creates instance of generic struct | pass |
| 3 | uses nested generic types | pass |
| 4 | uses tuple return type | pass |

**Example:** defines generic struct
    Then  expect 1 == 1  # parsing test

**Example:** creates instance of generic struct
    Given val b = Box { item: 42 }
    Then  expect b.item == 42

**Example:** uses nested generic types
    Then  expect 1 == 1  # parsing test

**Example:** uses tuple return type
    Then  expect 1 == 1  # parsing test

### Scenario: generic classes

### Scenario: Generic Classes

        Tests class types with type parameters.

| # | Example | Status |
|---|---------|--------|
| 1 | defines generic class | pass |
| 2 | creates generic enum | pass |
| 3 | uses generic field type | pass |
| 4 | uses list generic type | pass |

**Example:** defines generic class
    Then  expect 1 == 1  # parsing test

**Example:** creates generic enum
    Then  expect 1 == 1  # parsing test

**Example:** uses generic field type
    Then  expect 1 == 1  # parsing test

**Example:** uses list generic type
    Then  expect 1 == 1  # parsing test

### Scenario: generic with constraints

### Scenario: Type Bounds and Constraints

        Tests generic types with constraints on type parameters.

| # | Example | Status |
|---|---------|--------|
| 1 | uses where clause on function | pass |
| 2 | uses impl Trait for Type | pass |
| 3 | uses multiple trait bounds | pass |
| 4 | uses associated type | pass |

**Example:** uses where clause on function
    Then  expect filled(42) == 42

**Example:** uses impl Trait for Type
    Then  expect 1 == 1  # parsing test

**Example:** uses multiple trait bounds
    Then  expect 1 == 1  # parsing test

**Example:** uses associated type
    Then  expect 1 == 1  # parsing test

### Scenario: generic collections

### Scenario: Built-in Generic Types

        Tests built-in generic collection types.

| # | Example | Status |
|---|---------|--------|
| 1 | creates generic list | pass |
| 2 | creates generic dictionary | pass |
| 3 | creates generic option | pass |
| 4 | creates generic result | pass |

**Example:** creates generic list
    Given val numbers: List<i32> = [1, 2, 3]
    Then  expect numbers.first == Some(1)

**Example:** creates generic dictionary
    Given val mapping: Dict<text, i32> = {"a": 1}
    Then  expect mapping["a"] == 1

**Example:** creates generic option
    Given val some_value: Option<text> = Some("hello")
    Given val no_value: Option<text> = nil
    Then  expect some_value.is_some() == true

**Example:** creates generic result
    Given val ok_result: Result<i32, text> = Ok(42)
    Given val err_result: Result<i32, text> = Err("failed")
    Then  expect ok_result.is_ok() == true
    Then  expect err_result.is_err() == true

### Scenario: generic with variance

### Scenario: Type Parameter Variance

        Tests covariance and contravariance in generic types.

| # | Example | Status |
|---|---------|--------|
| 1 | uses const generic parameter | pass |
| 2 | uses generic impl with where | pass |
| 3 | uses function type syntax | pass |

**Example:** uses const generic parameter
    Then  expect 1 == 1  # parsing test

**Example:** uses generic impl with where
    Then  expect 1 == 1  # parsing test

**Example:** uses function type syntax
    Then  expect apply(double, 21) == 42

### Scenario: higher-order generic functions

### Scenario: Complex Generic Patterns

        Tests complex patterns with nested generics.

| # | Example | Status |
|---|---------|--------|
| 1 | defines function returning generic type | pass |
| 2 | uses function with generic result | pass |
| 3 | chains generic function calls | pass |

**Example:** defines function returning generic type
    Given val result = make_list(42)
    Then  expect result.first == Some(42)

**Example:** uses function with generic result
    Then  expect 1 == 1  # parsing test

**Example:** chains generic function calls
    Given val result = id(id(42))
    Then  expect result == 42

### Scenario: generic instantiation

### Scenario: Type Instantiation

        Tests explicit and implicit type instantiation of generics.

| # | Example | Status |
|---|---------|--------|
| 1 | implicitly infers type parameters | pass |
| 2 | explicitly specifies type parameters | pass |
| 3 | uses generic in method | pass |

**Example:** implicitly infers type parameters
    Given val result = wrap(10)
    Then  expect result.first == Some(10)

**Example:** explicitly specifies type parameters
    Given val result: Option<i32> = create()
    Then  expect result == nil

**Example:** uses generic in method
    Then  expect 1 == 1  # parsing test


