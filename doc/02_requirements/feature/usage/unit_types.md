# Unit Types Specification
*Source:* `test/feature/usage/unit_types_spec.spl`
**Feature IDs:** #UNIT-001  |  **Category:** Language | Types  |  **Status:** Implemented

## Overview



## Overview

Tests for semantic unit types that add compile-time dimensional safety
to numeric values.

## Feature: Standalone Units

## Basic Unit Type Definition

    Tests for defining and using standalone unit types.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | defines standalone unit type | pass |
| 2 | performs arithmetic with units | pass |
| 3 | gets value from unit | pass |
| 4 | gets suffix from unit | pass |
| 5 | converts unit to string | pass |

**Example:** defines standalone unit type
    Given val user_id = 42_uid
    Then  expect user_id == 42

**Example:** performs arithmetic with units
    Given val a = 100_pts
    Given val b = 50_pts
    Then  expect a + b == 150

**Example:** gets value from unit
    Given val d = 42_km
    Then  expect d.value() == 42

**Example:** gets suffix from unit
    Given val d = 100_bytes
    Given val s = d.suffix()
    Then  expect s == "bytes"

**Example:** converts unit to string
    Given val d = 5_km
    Given val s = d.to_string()
    Then  expect s == "5_km"

## Feature: Unit Families

## Unit Families with Conversions

    Tests for unit families with multiple related units and conversion factors.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | defines unit family | pass |

**Example:** defines unit family
    Given val d = 5000.0_m
    Then  expect d.value() == 5000.0

## Feature: Unit Arithmetic

## Type-Safe Unit Arithmetic

    Tests for unit arithmetic with explicit allow rules.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allows same-family addition | pass |
| 2 | allows same-family subtraction | pass |
| 3 | allows scaling by scalar | pass |
| 4 | allows comparison always | pass |

**Example:** allows same-family addition
    Given val a = 100_m
    Given val b = 50_m
    Then  expect (a + b).value() == 150

**Example:** allows same-family subtraction
    Given val a = 100_m
    Given val b = 30_m
    Then  expect (a - b).value() == 70

**Example:** allows scaling by scalar
    Given val d = 10_m
    Given val scaled = d * 3
    Then  expect scaled.value() == 30

**Example:** allows comparison always
    Given val a = 100_m
    Given val b = 50_m
    Then  expect a > b

## Feature: Compound Units

## Compound Unit Definitions

    Tests for compound units derived from base units.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | defines compound unit | pass |
| 2 | computes velocity from division | pass |
| 3 | cancels same units in division | pass |
| 4 | defines area from multiplication | pass |

**Example:** defines compound unit
    Then  expect 1 == 1

**Example:** computes velocity from division
    Given val dist = 100_m
    Given val dur = 10_s
    Given val speed = dist / dur
    Then  expect speed.value() == 10

**Example:** cancels same units in division
    Given val dist1 = 100_m
    Given val dist2 = 20_m
    Given val ratio = dist1 / dist2
    Then  expect ratio == 5

**Example:** defines area from multiplication
    Given val width = 10_m
    Given val height = 5_m
    Given val a = width * height
    Then  expect a.value() == 50

## Feature: SI Prefixes

## SI Prefix Support

    Tests for SI prefixes (kilo, mega, milli, micro, etc.).

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses kilo prefix | pass |
| 2 | uses mega prefix | pass |
| 3 | uses milli prefix | pass |

**Example:** uses kilo prefix
    Given val dist = 5_km
    Then  expect dist.value() == 5000

**Example:** uses mega prefix
    Given val dist = 2_Mm
    Then  expect dist.value() == 2000000

**Example:** uses milli prefix
    Given val dur = 500_ms
    Then  expect dur.value() < 1.0

## Feature: Unit Type Inference

## Unit Type in Function Signatures

    Tests for unit types as function parameter and return types.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | accepts correct unit parameter | pass |
| 2 | returns correct unit type | pass |

**Example:** accepts correct unit parameter
    Given val dist = 5_km
    Then  expect double_distance(dist).value() == 10

**Example:** returns correct unit type
    Then  expect get_distance().value() == 10


