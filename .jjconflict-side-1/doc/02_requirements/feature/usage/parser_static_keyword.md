# parser static keyword
*Source:* `test/feature/usage/parser_static_keyword_spec.spl`

## Feature: Static methods in classes

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses static method in class | pass |
| 2 | calls static method without instance | pass |
| 3 | parses static method with no parameters | pass |
| 4 | parses static method returning text | pass |

**Example:** parses static method in class
    Then  expect Math__add(2, 3) == 5

**Example:** calls static method without instance
    Then  expect Utils__double(5) == 10

**Example:** parses static method with no parameters
    Then  expect Counter__get_version() == 1

**Example:** parses static method returning text
    Then  expect Formatter__format() == "formatted"

## Feature: Static methods in impl blocks

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses static method in impl block | pass |
| 2 | parses multiple static methods in impl | pass |

**Example:** parses static method in impl block
    Given val p = Point__origin()
    Then  expect p.x == 0
    Then  expect p.y == 0

**Example:** parses multiple static methods in impl
    Given val sq = Rectangle__square(10.0)
    Then  expect sq.width == 10.0
    Then  expect sq.height == 10.0

## Feature: Static vs instance methods

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | distinguishes static from instance methods | pass |
| 2 | parses class with both static and instance methods | pass |

**Example:** distinguishes static from instance methods
    Given val ex = Example__create()
    Then  expect ex.get_value() == 42

**Example:** parses class with both static and instance methods
    Given val logger = Logger__default_logger()
    Then  expect logger.name == "default"

## Feature: Static methods as factories

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses static method as constructor alternative | pass |
| 2 | uses static method with parameters | pass |

**Example:** uses static method as constructor alternative
    Given val c = Color__red()
    Then  expect c.r == 255
    Then  expect c.g == 0
    Then  expect c.b == 0

**Example:** uses static method with parameters
    Given val cfg = Config__new(8080, "localhost")
    Then  expect cfg.port == 8080

## Feature: Static method visibility

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses public static method | pass |
| 2 | parses private static method | pass |

**Example:** parses public static method
    Then  expect PublicUtils__helper() == 100

**Example:** parses private static method
    Then  expect PrivateUtils__internal() == 200

## Feature: Static methods with generics

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses static generic method | pass |

**Example:** parses static generic method
    Then  expect Container__create(42) == 42
    Then  expect Container__create("text") == "text"

## Feature: Static methods calling other static methods

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | calls static method from another static method | pass |

**Example:** calls static method from another static method
    Then  expect Calculator__add_three(1, 2, 3) == 6

## Feature: Static methods with default parameters

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses static method with default parameter | pass |

**Example:** parses static method with default parameter
    Then  expect Builder__build() == 10
    Then  expect Builder__build(20) == 20

## Feature: Static methods returning complex types

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses static method returning array | pass |
| 2 | parses static method returning option | pass |

**Example:** parses static method returning array
    Given val arr = ArrayFactory__create_array()
    Then  expect arr.len() == 3

**Example:** parses static method returning option
    Given val opt = OptionFactory__some_value()
    Then  expect opt.is_some() == true

## Feature: Static method edge cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses static method with no return type | pass |
| 2 | parses static method with complex expression | pass |
| 3 | parses nested static method calls | pass |

**Example:** parses static method with no return type
    Then  expect true

**Example:** parses static method with complex expression
    Given val x = 10
    Given val y = 20
    Then  expect Complex__compute() == 35

**Example:** parses nested static method calls
    Then  expect Nested__level1() == 42

## Feature: Static methods in async contexts

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses async static method | pass |

**Example:** parses async static method
    Then  expect true


