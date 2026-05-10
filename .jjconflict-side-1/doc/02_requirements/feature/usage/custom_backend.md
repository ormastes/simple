# custom backend
*Source:* `test/feature/usage/custom_backend_spec.spl`

## Feature: Custom Collection Backends

### Scenario: ArrayList Implementation

| # | Example | Status |
|---|---------|--------|
| 1 | should create ArrayList from array literal | pass |
| 2 | should support push | pass |
| 3 | should support pop | pass |
| 4 | should support get | pass |

**Example:** should create ArrayList from array literal
    Given val arr: ArrayList = [1, 2, 3]
    Then  expect(arr.len()).to_equal(3)

**Example:** should support push
    Given var arr: ArrayList = [1, 2]
    Then  expect(arr.len()).to_equal(3)

**Example:** should support pop
    Given var arr: ArrayList = [1, 2, 3]
    Given val last = arr.pop()
    Then  expect last == 3
    Then  expect arr.len() == 2

**Example:** should support get
    Given val arr: ArrayList = [10, 20, 30]
    Then  expect(arr.get(0)).to_equal(10)
    Then  expect(arr.get(2)).to_equal(30)

### Scenario: HashMap Implementation

| # | Example | Status |
|---|---------|--------|
| 1 | should create HashMap from dict literal | pass |
| 2 | should support get | pass |
| 3 | should support insert | pass |

**Example:** should create HashMap from dict literal
    Given val map: HashMap = {"a": 1, "b": 2}
    Then  expect(map.len()).to_equal(2)

**Example:** should support get
    Given val map: HashMap = {"a": 1, "b": 2}
    Then  expect map["a"] == 1
    Then  expect map["b"] == 2

**Example:** should support insert
    Given var map: HashMap = {"a": 1}
    Then  expect map["b"] == 2


