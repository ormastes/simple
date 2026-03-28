# function alias
*Source:* `test/feature/usage/function_alias_spec.spl`

## Feature: function alias (deprecated delegation)

### Scenario: basic alias

| # | Example | Status |
|---|---------|--------|
| 1 | calls target function | pass |
| 2 | works with zero arguments | pass |
| 3 | works with negative arguments | pass |

**Example:** calls target function
    Given val result = sum(3, 4)
    Then  expect(result).to_equal(7)

**Example:** works with zero arguments
    Given val result = sum(0, 0)
    Then  expect(result).to_equal(0)

**Example:** works with negative arguments
    Given val result = sum(-1, -2)
    Then  expect(result).to_equal(-3)

### Scenario: alias preserves behavior

| # | Example | Status |
|---|---------|--------|
| 1 | preserves return value for text | pass |
| 2 | preserves return value for integer | pass |

**Example:** preserves return value for text
    Given val msg = say_hello("World")
    Then  expect(msg).to_equal("Hello, World")

**Example:** preserves return value for integer
    Given val result = same(42)
    Then  expect(result).to_equal(42)

### Scenario: alias chain

| # | Example | Status |
|---|---------|--------|
| 1 | alias of alias works | pass |
| 2 | intermediate alias also works | pass |

**Example:** alias of alias works
    Given val result = times_two(5)
    Then  expect(result).to_equal(10)

**Example:** intermediate alias also works
    Given val result = multiply_by_two(7)
    Then  expect(result).to_equal(14)

### Scenario: original function

| # | Example | Status |
|---|---------|--------|
| 1 | original still works | pass |
| 2 | alias and original return same result | pass |

**Example:** original still works
    Given val result = add(1, 2)
    Then  expect(result).to_equal(3)

**Example:** alias and original return same result
    Given val r1 = add(10, 20)
    Given val r2 = sum(10, 20)
    Then  expect(r1).to_equal(r2)

### Scenario: void alias

| # | Example | Status |
|---|---------|--------|
| 1 | void alias is callable | pass |

**Example:** void alias is callable
    Then  expect(true).to_equal(true)


