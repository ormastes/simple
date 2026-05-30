# Class Invariant Specification
*Source:* `test/feature/usage/class_invariant_spec.spl`
**Feature IDs:** #CONTRACT-INV-001 to #CONTRACT-INV-018  |  **Category:** Type System | Contracts  |  **Status:** Implemented

## Overview



Tests that class invariants are properly checked:
- After constructor execution (even if constructor is private)
- Before/after public method execution
- NOT checked for private methods

## Syntax

```simple
class Counter:
    value: i64

    invariant:
        self.value >= 0

    static fn new() -> Counter:
        Counter(value: 0)

    me increment():
        self.value = self.value + 1
```

## Feature: Constructor Invariant Checks

## Constructor Exit Invariants

    Tests that constructors check class invariants on exit.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | checks invariant after constructor | pass |
| 2 | checks multiple invariants after constructor | pass |
| 3 | private constructor gets invariant check | pass |
| 4 | constructor with precondition and invariant | pass |

**Example:** checks invariant after constructor
    Given val c = Counter__new(10)
    Then  expect c.value == 10

**Example:** checks multiple invariants after constructor
    Given val bc = BoundedCounter__new(5, 100)
    Then  expect bc.value == 5

**Example:** private constructor gets invariant check
    Given val acc = Account__create_with_deposit(100)
    Then  expect acc.balance == 100

**Example:** constructor with precondition and invariant
    Given val pv = PositiveValue__new(42)
    Then  expect pv.value == 42

## Feature: Public Method Invariant Checks

## Method Entry/Exit Invariants

    Tests that public methods check invariants at entry and exit.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | public method checks invariants | pass |
| 2 | private method skips invariants | pass |
| 3 | complex invariant with field comparison | pass |

**Example:** public method checks invariants
    Given var c = Counter__new()
    Then  expect c.value == 1
    Then  expect c.value == 0

**Example:** private method skips invariants
    Given var c = Counter__new()
    Then  expect c.value == 42

**Example:** complex invariant with field comparison
    Given var r = Range__new(0, 10)
    Then  expect r.max == 15

## Feature: Multiple Classes with Invariants

## Class Separation

    Tests that each class has its own invariants.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | separate invariants per class | pass |

**Example:** separate invariants per class
    Given val acc = Account__new(100)
    Given val tx = Transaction__new(50, 1234567890)
    Then  expect acc.balance == 100
    Then  expect tx.amount == 50

## Feature: Inheritance and Invariants

## Inherited Invariants

    Tests that child classes maintain parent invariants.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | child maintains parent invariant | pass |

**Example:** child maintains parent invariant
    Given val car = Car__new(50)
    Then  expect car.speed == 0
    Then  expect car.fuel == 50

## Feature: Class Invariant Edge Cases

## Special Cases

    Tests edge cases for class invariants.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | class without invariant works | pass |
| 2 | invariant can reference pure methods | pass |

**Example:** class without invariant works
    Given val s = Simple__new(42)
    Then  expect s.get_value() == 42

**Example:** invariant can reference pure methods
    Given val vh = ValueHolder__new(42)
    Then  expect vh.value == 42

## Feature: Constructor Visibility

## Constructor Detection

    Tests invariants with different constructor visibilities.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | explicitly public constructor gets invariants | pass |
| 2 | constructor detected by name | pass |

**Example:** explicitly public constructor gets invariants
    Given val p = Public__new(42)
    Then  expect p.value == 42

**Example:** constructor detected by name
    Given val c1 = Counter__new()
    Given val c2 = Counter__from_value(42)
    Then  expect c1.count == 0
    Then  expect c2.count == 42

## Feature: Complete Class Contract Integration

## Full Contract Specification

    Tests complete class with all contract types.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | bank account with full contracts | pass |

**Example:** bank account with full contracts
    Given var acc = BankAccount__from_balance("Alice", 100)
    Then  expect acc.get_balance() == 150
    Given val success = acc.withdraw(30)
    Then  expect success
    Then  expect acc.get_balance() == 120

## Feature: Factory Method Invariants

## Factory Methods

    Tests factory methods get invariant checks.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | factory methods get invariants | pass |

**Example:** factory methods get invariants
    Given val c1 = Config__create_default()
    Given val c2 = Config__from_timeout(60)
    Given val c3 = Config__with_retries(5)
    Then  expect c1.timeout == 30
    Then  expect c2.timeout == 60
    Then  expect c3.retries == 5

## Feature: Struct Invariants

## Struct Contracts

    Tests structs work the same as classes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | struct has invariant checks | pass |

**Example:** struct has invariant checks
    Given val p = Point__new(3, 4)
    Then  expect p.distance_squared() == 25


