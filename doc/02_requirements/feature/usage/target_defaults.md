# target defaults
*Source:* `test/feature/usage/target_defaults_spec.spl`

## Overview

Target-Based Mutability Defaults - SSpec Tests
Decision #9: --target=embedded makes arrays immutable by default

Category: Collections
Status: Partially Implemented

## Feature: Target-Based Mutability Defaults

### Scenario: General Mode (Default)

| # | Example | Status |
|---|---------|--------|
| 1 | makes arrays mutable by default | pass |
| 2 | makes dicts mutable by default | pass |

**Example:** makes arrays mutable by default
    Given var arr = [1, 2, 3]
    Then  expect arr.len() == 4
    Then  expect arr[3] == 4

**Example:** makes dicts mutable by default
    Given val dict = {"a": 1}
    Then  expect dict["b"] == 2


