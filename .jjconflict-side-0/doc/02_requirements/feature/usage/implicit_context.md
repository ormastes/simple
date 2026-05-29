# implicit context
*Source:* `test/feature/usage/implicit_context_spec.spl`

## Feature: Feature 7: Implicit Context Parameters

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | context variable is accessible in functions | pass |
| 2 | functions share the same context variable | pass |
| 3 | last logged message is from deepest function call | pass |
| 4 | context variable can be swapped for different loggers | pass |
| 5 | save-set-restore pattern preserves outer context | pass |
| 6 | nil context is default before any with_context | pass |

**Example:** context variable is accessible in functions
    Given val logger = TestLogger(messages: 0, last_msg: "")
    Then  expect(__ctx_logger.count()).to_be_greater_than(0)

**Example:** functions share the same context variable
    Given val logger = TestLogger(messages: 0, last_msg: "")
    Then  expect(__ctx_logger.count()).to_equal(3)

**Example:** last logged message is from deepest function call
    Given val logger = TestLogger(messages: 0, last_msg: "")
    Then  expect(__ctx_logger.last()).to_start_with("lexing:")

**Example:** context variable can be swapped for different loggers
    Given val logger1 = TestLogger(messages: 0, last_msg: "first")
    Given val logger2 = TestLogger(messages: 0, last_msg: "second")
    Given val count1 = __ctx_logger.count()
    Given val count2 = __ctx_logger.count()
    Then  expect(count1).to_equal(1)
    Then  expect(count2).to_equal(1)

**Example:** save-set-restore pattern preserves outer context
    Given val outer_logger = TestLogger(messages: 0, last_msg: "outer")
    Given val inner_logger = TestLogger(messages: 0, last_msg: "inner")
    Given val __saved_logger_0 = __ctx_logger
    Then  expect(__ctx_logger.last()).to_start_with("lexing: y")
    Then  expect(__ctx_logger.count()).to_equal(1)  # outer logger only saw "y"

**Example:** nil context is default before any with_context
    Given val is_nil = __ctx_logger == nil
    Then  expect(is_nil).to_equal(true)

## Feature: Feature 7: Multiple Context Variables

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | multiple context vars are independent | pass |
| 2 | setting one ctx var does not affect others | pass |

**Example:** multiple context vars are independent
    Given val lg = TestLogger(messages: 0, last_msg: "")
    Then  expect(__ctx_logger.last()).to_contain("production")

**Example:** setting one ctx var does not affect others
    Given val lg = TestLogger(messages: 0, last_msg: "unchanged")
    Given val unchanged = __ctx_logger.last() == "unchanged"
    Then  expect(unchanged).to_equal(true)


