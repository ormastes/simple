# Parser Syntax Validation Specification
*Source:* `test/feature/usage/parser_syntax_validation_spec.spl`
**Feature IDs:** #PARSER-VAL-001 to #PARSER-VAL-015  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview




Tests that the parser correctly validates syntax and provides helpful
error messages. Includes tests for correct Simple syntax that should
parse successfully.

## Key Validations

- Proper indentation handling
- Comment parsing (single-line, multi-line)
- Whitespace handling
- Newline requirements
- Block structure validation

## Feature: Comment Parsing

## Single and Multi-Line Comments

    Tests that comments are correctly parsed and ignored.

### Scenario: single-line comments

| # | Example | Status |
|---|---------|--------|
| 1 | parses code with trailing comment | pass |
| 2 | parses comment-only lines | pass |
| 3 | parses multiple comment styles | pass |

**Example:** parses code with trailing comment
    Given val x = 42  # This is a comment
    Then  expect x == 42

**Example:** parses comment-only lines
    Given val x = 42
    Then  expect x == 42

**Example:** parses multiple comment styles
    Given val x = 42  # Hash comment
    Then  expect x == 42

### Scenario: multi-line comments

This is a multi-line comment
            that spans several lines.

| # | Example | Status |
|---|---------|--------|
| 1 | parses block comment | pass |
| 2 | parses inline docstring | pass |

**Example:** parses block comment
    Given val x = 42
    Then  expect x == 42

**Example:** parses inline docstring
    Then  expect documented() == 42

## Feature: Indentation Handling

## Python-Style Indentation

    Tests that indentation-based blocks are correctly parsed.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple indented block | pass |
| 2 | parses nested indentation | pass |
| 3 | parses dedent correctly | pass |
| 4 | parses multiple statements in block | pass |

**Example:** parses simple indented block
    Given val x = 42
    Then  expect x == 42

**Example:** parses nested indentation
    Given val x = 42
    Then  expect x == 42

**Example:** parses dedent correctly
    Given var total = 0
    Then  expect total == 42

**Example:** parses multiple statements in block
    Given var a = 0
    Given var b = 0
    Given val c = 12
    Then  expect a + b == 42

## Feature: Correct Keyword Usage

## Simple Language Keywords

    Tests that Simple keywords are used correctly.

### Scenario: variable keywords

| # | Example | Status |
|---|---------|--------|
| 1 | uses val for immutable | pass |
| 2 | uses var for mutable | pass |
| 3 | uses let for binding | pass |

**Example:** uses val for immutable
    Given val x = 42
    Then  expect x == 42

**Example:** uses var for mutable
    Given var x = 0
    Then  expect x == 42

**Example:** uses let for binding
    Then  expect x == 42

### Scenario: function keywords

| # | Example | Status |
|---|---------|--------|
| 1 | uses fn for function | pass |
| 2 | uses return for early return | pass |

**Example:** uses fn for function
    Then  expect get_value() == 42

**Example:** uses return for early return
    Then  expect check(42) == 42

### Scenario: control flow keywords

| # | Example | Status |
|---|---------|--------|
| 1 | uses elif not else if | pass |

**Example:** uses elif not else if
    Then  expect classify(5) == "positive"

## Feature: Boolean Literal Validation

## Correct Boolean Syntax

    Tests that Simple uses lowercase true/false, not Python's True/False.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses lowercase true | pass |
| 2 | uses lowercase false | pass |
| 3 | uses booleans in conditions | pass |

**Example:** uses lowercase true
    Given val x = true
    Then  expect x == true

**Example:** uses lowercase false
    Given val x = false
    Then  expect x == false

**Example:** uses booleans in conditions
    Then  expect true
    Then  expect true

## Feature: Nil Value Validation

## Correct Nil Syntax

    Tests that Simple uses nil, and None is for Option type.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses nil for null value | pass |
| 2 | uses None for Option | pass |
| 3 | uses Some for Option with value | pass |

**Example:** uses nil for null value
    Given val x = nil
    Then  expect x == nil

**Example:** uses None for Option
    Given val opt: Option<i64> = None
    Then  expect not opt.?

**Example:** uses Some for Option with value
    Given val opt = Some(42)
    Then  expect opt.?

## Feature: Type Annotation Validation

## Correct Type Syntax

    Tests that type annotations use correct Simple syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses colon for type annotation | pass |
| 2 | uses arrow for return type | pass |
| 3 | uses angle brackets for generics | pass |
| 4 | uses Option for optional types | pass |

**Example:** uses colon for type annotation
    Given val x: i64 = 42
    Then  expect x == 42

**Example:** uses arrow for return type
    Then  expect get_value() == 42

**Example:** uses angle brackets for generics
    Then  expect identity(42) == 42

**Example:** uses Option for optional types
    Given val opt: Option<i64> = Some(42)
    Then  expect opt.unwrap() == 42

## Feature: String Syntax Validation

## Correct String Literals

    Tests that strings use correct Simple syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses double quotes for interpolated strings | pass |
| 2 | uses single quotes for raw strings | pass |
| 3 | uses r prefix for raw double-quoted | pass |

**Example:** uses double quotes for interpolated strings
    Given val name = "World"
    Given val greeting = "Hello, {name}!"
    Then  expect greeting == "Hello, World!"

**Example:** uses single quotes for raw strings
    Given val raw = 'Hello{NL}World'
    Then  expect raw.contains("\{NL}")

**Example:** uses r prefix for raw double-quoted
    Given val raw = r"Path\to\file"
    Then  expect raw.contains("\\")

## Feature: Collection Syntax Validation

## Correct Collection Literals

    Tests that collections use correct Simple syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses square brackets for arrays | pass |
| 2 | uses parentheses for tuples | pass |
| 3 | uses braces for dictionaries | pass |

**Example:** uses square brackets for arrays
    Given val arr = [1, 2, 3]
    Then  expect arr.len() == 3

**Example:** uses parentheses for tuples
    Given val t = (1, 2, 3)
    Then  expect t.0 == 1

**Example:** uses braces for dictionaries
    Given val d = {"key": 42}
    Then  expect d["key"] == 42

## Feature: Struct Instantiation Validation

## Correct Struct Construction

    Tests that structs are instantiated with correct syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses braces for struct literal | pass |
| 2 | uses colon in struct literal | pass |

**Example:** uses braces for struct literal
    Given val p = Point { x: 10, y: 20 }
    Then  expect p.x == 10

**Example:** uses colon in struct literal
    Given val d = Data { value: 42 }
    Then  expect d.value == 42

## Feature: Pattern Matching Validation

## Correct Match Syntax

    Tests that pattern matching uses correct Simple syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses case keyword for patterns | pass |
| 2 | uses if for guards | pass |
| 3 | uses double colon for enum variants | pass |

**Example:** uses case keyword for patterns
    Then  expect classify(0) == "zero"

**Example:** uses if for guards
    Then  expect classify(-5) == "negative"

**Example:** uses double colon for enum variants
    Then  expect check(Status.Ok) == "ok"


