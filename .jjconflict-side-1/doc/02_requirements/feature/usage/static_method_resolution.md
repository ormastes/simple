# static method resolution
*Source:* `test/feature/usage/static_method_resolution_spec.spl`

## Feature: Static Method Resolution

### Scenario: Basic static method resolution

| # | Example | Status |
|---|---------|--------|
| 1 | resolves simple static method call | pass |
| 2 | resolves static method with parameters | pass |
| 3 | resolves static method returning object | pass |

**Example:** resolves simple static method call
    Given val result = TestClass__get_value()
    Then  expect result == 42

**Example:** resolves static method with parameters
    Given val result = Math__add(5, 3)
    Then  expect result == 8

**Example:** resolves static method returning object
    Given val p = Point__origin()
    Then  expect p.x == 0
    Then  expect p.y == 0

### Scenario: Static vs instance method distinction

| # | Example | Status |
|---|---------|--------|
| 1 | correctly resolves static method vs instance method | pass |
| 2 | allows same name for static and instance methods | pass |

**Example:** correctly resolves static method vs instance method
    Given val counter = Counter__start()
    Given val value = counter.get()
    Then  expect value == 0

**Example:** allows same name for static and instance methods
    Given val static_result = Dual__get_name()
    Given val instance = Dual(name: "Instance")
    Given val instance_result = instance.get_name()
    Then  expect static_result == "Static"
    Then  expect instance_result == "Instance"

### Scenario: Static method chaining

| # | Example | Status |
|---|---------|--------|
| 1 | chains static method call with instance method | pass |
| 2 | calls multiple static methods in sequence | pass |

**Example:** chains static method call with instance method
    Given val result = Builder__new().double()
    Then  expect result == 20

**Example:** calls multiple static methods in sequence
    Given val a = Factory__create_a()
    Given val b = Factory__create_b()
    Then  expect (a + b) == 3

### Scenario: Static methods calling other methods

| # | Example | Status |
|---|---------|--------|
| 1 | static method calls another static method | pass |
| 2 | static method creates object and calls instance method | pass |

**Example:** static method calls another static method
    Given val result = Calculator__sum_of_squares(3, 4)
    Then  expect result == 25

**Example:** static method creates object and calls instance method
    Given val (x, y) = t
    Given val result = Point__from_tuple((5, 3)).sum()
    Then  expect result == 8

### Scenario: Static method in structs

| # | Example | Status |
|---|---------|--------|
| 1 | resolves static method on struct | pass |
| 2 | resolves multiple static methods on struct | pass |

**Example:** resolves static method on struct
    Given val config = Config__default()
    Then  expect config.value == 100

**Example:** resolves multiple static methods on struct
    Given val l = Settings__low()
    Given val m = Settings__medium()
    Given val h = Settings__high()
    Then  expect l.level == 1
    Then  expect m.level == 5
    Then  expect h.level == 10

### Scenario: Error cases

| # | Example | Status |
|---|---------|--------|
| 1 | reports error for non-existent static method | pass |
| 2 | reports error for calling instance method as static | pass |


