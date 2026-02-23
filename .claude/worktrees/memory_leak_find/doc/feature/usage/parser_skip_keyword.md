# parser skip keyword
*Source:* `test/feature/usage/parser_skip_keyword_spec.spl`

## Feature: Skip keyword - lexer and token recognition

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | recognizes skip as a keyword token | pass |
| 2 | allows skip_func as function name | pass |
| 3 | distinguishes skip keyword from skip variable name | pass |
| 4 | allows skip in string literals | pass |

**Example:** recognizes skip as a keyword token
    Given val keywords = ["break", "continue", "pass", "defer", "skip", "return"]
    Then  expect keywords.len() == 6

**Example:** allows skip_func as function name
    Then  expect skip_func() == 42

**Example:** distinguishes skip keyword from skip variable name
    Given val skip_count = 10
    Then  expect skip_count == 10

**Example:** allows skip in string literals
    Given val message = "Please skip this step"
    Then  expect message.contains("skip")

## Feature: Skip keyword - basic statement parsing

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses skip as standalone statement | pass |
| 2 | parses skip with indented block | pass |
| 3 | parses multiple skip statements | pass |

**Example:** parses skip as standalone statement
    Given var executed = true
    Then  expect executed == true

**Example:** parses skip with indented block
    Given val x = 1
    Given val y = 2
    Then  expect true

**Example:** parses multiple skip statements
    Then  expect true

## Feature: Skip keyword - control flow interactions

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses skip inside if block | pass |
| 2 | parses skip inside loop | pass |
| 3 | parses skip with break in same function | pass |
| 4 | parses skip with continue in same function | pass |
| 5 | parses skip with return in same function | pass |

**Example:** parses skip inside if block
    Given val condition = true
    Then  expect true

**Example:** parses skip inside loop
    Then  expect true

**Example:** parses skip with break in same function
    Then  expect true

**Example:** parses skip with continue in same function
    Given var count = 0
    Then  expect count == 3

**Example:** parses skip with return in same function
    Then  expect with_skip_and_return() == 42

## Feature: Skip keyword - function and method contexts

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses skip in function body | pass |
| 2 | parses skip in method body | pass |
| 3 | parses skip in static method | pass |
| 4 | parses skip in lambda | pass |

**Example:** parses skip in function body
    Then  expect test_function() == "completed"

**Example:** parses skip in method body
    Given val obj = TestClass()
    Then  expect obj.test_method() == "method completed"

**Example:** parses skip in static method
    Then  expect StaticTest.static_method() == "static completed"

**Example:** parses skip in lambda
    Given val lambda_with_skip = \x:
    Then  expect lambda_with_skip(5) == 10

## Feature: Skip keyword - class and struct contexts

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses skip in class method | pass |
| 2 | parses skip in impl block method | pass |

**Example:** parses skip in class method
    Given val c = Container(value: 100)
    Then  expect c.process() == 100

**Example:** parses skip in impl block method
    Given val p = Point(x: 3, y: 4)
    Then  expect p.distance() == 0.0

## Feature: Skip keyword - async contexts

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses skip in async function | pass |
| 2 | parses skip before await | pass |

**Example:** parses skip in async function
    Then  expect true

**Example:** parses skip before await
    Given val result = 42
    Then  expect true

## Feature: Skip keyword - match and pattern contexts

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses skip in match arm | pass |
| 2 | parses skip in multiple match arms | pass |

**Example:** parses skip in match arm
    Given val x = 5
    Given val result = match x:
    Then  expect result == "other"

**Example:** parses skip in multiple match arms
    Given val value = 10
    Given var count = 0
    Then  expect count == 1

## Feature: Skip keyword - expression contexts

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses skip before expression | pass |
| 2 | parses skip between declarations | pass |
| 3 | parses skip in complex expression flow | pass |

**Example:** parses skip before expression
    Given val result = 2 + 2
    Then  expect with_skip_expr() == 4

**Example:** parses skip between declarations
    Given val a = 1
    Given val b = 2
    Then  expect multi_decl() == 3

**Example:** parses skip in complex expression flow
    Then  expect complex_flow(5) == 10
    Then  expect complex_flow(-3) == -3

## Feature: Skip keyword - error handling contexts

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses skip in try-catch block | pass |
| 2 | parses skip before result return | pass |

**Example:** parses skip in try-catch block
    Then  expect with_try() == "ok"

**Example:** parses skip before result return
    Then  expect result_with_skip() == 42

## Feature: Skip keyword - edge cases and boundaries

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses skip at start of file | pass |
| 2 | parses skip at end of function | pass |
| 3 | parses skip with empty block | pass |
| 4 | parses nested skip statements | pass |
| 5 | parses skip with comment | pass |
| 6 | parses skip with multiline comment | pass |

**Example:** parses skip at start of file
    Then  expect true

**Example:** parses skip at end of function
    Given val x = 1
    Then  expect true

**Example:** parses skip with empty block
    Then  expect true

**Example:** parses nested skip statements
    Then  expect true

**Example:** parses skip with comment
    Then  expect true

**Example:** parses skip with multiline comment
    Then  expect true

## Feature: Skip keyword - indentation and whitespace

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses skip with various indentation | pass |
| 2 | parses skip with no trailing whitespace | pass |
| 3 | parses skip with blank lines after | pass |

**Example:** parses skip with various indentation
    Then  expect true

**Example:** parses skip with no trailing whitespace
    Given val x = 1
    Then  expect x == 1

**Example:** parses skip with blank lines after
    Given val y = 2
    Then  expect y == 2

## Feature: Skip keyword - semantics and runtime behavior

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | skip statement does not prevent execution | pass |
| 2 | skip does not affect variable scope | pass |
| 3 | skip does not affect return value | pass |
| 4 | skip does not affect loop iteration | pass |

**Example:** skip statement does not prevent execution
    Given var executed = false
    Then  expect executed == true

**Example:** skip does not affect variable scope
    Given val scoped = 100
    Then  expect scoped == 100

**Example:** skip does not affect return value
    Then  expect returns_with_skip() == "value"

**Example:** skip does not affect loop iteration
    Given var iterations = 0
    Then  expect iterations == 5

## Feature: Skip keyword - future test framework integration

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allows skip for test tagging preparation | pass |
| 2 | parses skip with test metadata | pass |

**Example:** allows skip for test tagging preparation
    Then  expect true

**Example:** parses skip with test metadata
    Then  expect true


