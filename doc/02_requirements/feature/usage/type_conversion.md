# type conversion
*Source:* `test/feature/usage/type_conversion_spec.spl`

## Overview

Type Annotation Conversion - SSpec Tests
Decision #7: val arr: ArrayList = [1, 2, 3] should auto-convert

Category: Collections
Status: Not Yet Implemented (deferred)

## Feature: Type Annotation Conversion

### Scenario: Basic Array Operations

| # | Example | Status |
|---|---------|--------|
| 1 | arrays work without type conversion | pass |

**Example:** arrays work without type conversion
    Given val arr = [1, 2, 3]
    Then  expect arr.len() == 3
    Then  expect arr[0] == 1


