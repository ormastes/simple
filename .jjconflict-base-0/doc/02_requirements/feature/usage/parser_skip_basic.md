# parser skip basic
*Source:* `test/feature/usage/parser_skip_basic_spec.spl`

## Feature: Skip keyword - basic functionality

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses skip as standalone statement | pass |
| 2 | parses skip with pass | pass |
| 3 | parses skip in if block | pass |
| 4 | parses skip in function body | pass |
| 5 | parses multiple skip statements | pass |
| 6 | parses skip before expression | pass |
| 7 | parses skip in loop | pass |
| 8 | skip does not prevent execution | pass |
| 9 | skip does not affect return value | pass |
| 10 | skip does not affect variable scope | pass |

**Example:** parses skip as standalone statement
    Given var executed = true
    Then  expect executed == true

**Example:** parses skip with pass
    Then  expect true

**Example:** parses skip in if block
    Given val condition = true
    Then  expect true

**Example:** parses skip in function body
    Then  expect test_function() == "completed"

**Example:** parses multiple skip statements
    Then  expect true

**Example:** parses skip before expression
    Given val result = 2 + 2
    Then  expect result == 4

**Example:** parses skip in loop
    Given var count = 0
    Then  expect count == 3

**Example:** skip does not prevent execution
    Given var executed = false
    Then  expect executed == true

**Example:** skip does not affect return value
    Then  expect returns_with_skip() == "value"

**Example:** skip does not affect variable scope
    Given val scoped = 100
    Then  expect scoped == 100


