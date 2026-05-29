# parser default keyword
*Source:* `test/feature/usage/parser_default_keyword_spec.spl`

## Feature: Default keyword in function parameters

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses default parameter value with = syntax | pass |
| 2 | parses multiple default parameters | pass |
| 3 | overrides single default parameter | pass |
| 4 | parses default with expressions | pass |
| 5 | parses default with arithmetic | pass |
| 6 | uses default in nested function | pass |

**Example:** parses default parameter value with = syntax
    Then  expect greet() == "Hello, World"
    Then  expect greet("Alice") == "Hello, Alice"

**Example:** parses multiple default parameters
    Given val range = create_range()
    Then  expect range[0] == 0
    Then  expect range[1] == 100

**Example:** overrides single default parameter
    Then  expect with_defaults() == 3
    Then  expect with_defaults(5) == 7
    Then  expect with_defaults(5, 10) == 15

**Example:** parses default with expressions
    Then  expect with_expr_default() == 1024

**Example:** parses default with arithmetic
    Then  expect compute() == 115

**Example:** uses default in nested function
    Then  expect outer() == 42

## Feature: Default keyword with types

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses default parameter with type annotation | pass |
| 2 | parses default text parameter | pass |
| 3 | parses default float parameter | pass |

**Example:** parses default parameter with type annotation
    Then  expect typed_default() == 0
    Then  expect typed_default(5) == 5

**Example:** parses default text parameter
    Then  expect with_text() == "default"
    Then  expect with_text("custom") == "custom"

**Example:** parses default float parameter
    Then  expect with_float() > 3.0

## Feature: Default keyword in methods

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses default in class method | pass |
| 2 | parses default in static method | pass |

**Example:** parses default in class method
    Given var c = Counter(value: 10)
    Then  expect c.value == 11

**Example:** parses default in static method
    Then  expect Factory.create() == 10
    Then  expect Factory.create(20) == 20

## Feature: Default keyword with collections

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses default empty array | pass |
| 2 | parses default array literal | pass |

**Example:** parses default empty array
    Then  expect with_array() == 0
    Then  expect with_array([1, 2, 3]) == 3

**Example:** parses default array literal
    Then  expect with_values() == 3

## Feature: Default keyword edge cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses default with boolean | pass |
| 2 | parses default with negative number | pass |
| 3 | parses default with string interpolation | pass |

**Example:** parses default with boolean
    Then  expect with_flag() == true
    Then  expect with_flag(false) == false

**Example:** parses default with negative number
    Then  expect with_negative() == -10

**Example:** parses default with string interpolation
    Given val default_name = "World"
    Then  expect greet_default() == "Hello, World"

## Feature: Default keyword combinations

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses mix of required and default parameters | pass |
| 2 | parses multiple functions with defaults | pass |

**Example:** parses mix of required and default parameters
    Then  expect mixed(10) == 15
    Then  expect mixed(10, 20) == 30

**Example:** parses multiple functions with defaults
    Then  expect first() == 1
    Then  expect second() == 2


