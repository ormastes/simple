# Range Step Specification
*Source:* `test/feature/usage/range_step_by_spec.spl`
**Feature IDs:** #RANGE-STEP  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



use std.text.{NL}

Ranges in Simple can be iterated with custom step values. This is primarily
used in slice syntax with the `[start:end:step]` notation, allowing iteration
over every Nth element or reversing sequences.

## Syntax

```simple
# Slice with step
arr[::2]       # Every other element (step=2)
arr[1::2]      # Every other starting from index 1
arr[::-1]      # Reversed
arr[1:5:2]     # Slice from 1 to 5 with step 2

# Range iteration (stdlib method)
for i in (0..10).step_by(2):
    print i    # 0, 2, 4, 6, 8
```

## Key Behaviors

- Step value can be positive (forward) or negative (reverse)
- Step of 1 is the default (every element)
- Step of -1 reverses the sequence
- Step of 2 selects every other element
- Works on arrays, strings, and any sliceable type

## Feature: Range Step (Slicing with Step)

## Slice Step Specification

    Slice step syntax allows selecting elements at regular intervals from
    sequences. This test suite verifies:
    - Basic step syntax `[::step]` for every Nth element
    - Slice with start, end, and step `[start:end:step]`
    - Reverse iteration with negative step `[::-1]`
    - Step on arrays and strings
    - Edge cases with empty results and bounds

### Scenario: basic step on arrays

| # | Example | Status |
|---|---------|--------|
| 1 | selects every other element with step 2 | pass |
| 2 | selects every third element with step 3 | pass |
| 3 | selects every fourth element | pass |

**Example:** selects every other element with step 2
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    Then  expect arr[::2] == [0, 2, 4, 6, 8]

**Example:** selects every third element with step 3
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    Then  expect arr[::3] == [0, 3, 6, 9]

**Example:** selects every fourth element
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
    Then  expect arr[::4] == [0, 4, 8]

### Scenario: step with start offset

| # | Example | Status |
|---|---------|--------|
| 1 | starts from index 1 with step 2 | pass |
| 2 | starts from index 2 with step 3 | pass |
| 3 | starts from middle of array | pass |

**Example:** starts from index 1 with step 2
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    Then  expect arr[1::2] == [1, 3, 5, 7, 9]

**Example:** starts from index 2 with step 3
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    Then  expect arr[2::3] == [2, 5, 8]

**Example:** starts from middle of array
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    Then  expect arr[5::2] == [5, 7, 9]

### Scenario: step with start and end

| # | Example | Status |
|---|---------|--------|
| 1 | slices range with step | pass |
| 2 | slices narrow range with step | pass |
| 3 | slices with step larger than range | pass |

**Example:** slices range with step
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    Then  expect arr[1:8:2] == [1, 3, 5, 7]

**Example:** slices narrow range with step
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    Then  expect arr[2:6:2] == [2, 4]

**Example:** slices with step larger than range
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    Then  expect arr[0:5:10] == [0]

### Scenario: negative step (reverse)

| # | Example | Status |
|---|---------|--------|
| 1 | reverses entire array | pass |
| 2 | reverses empty array | pass |
| 3 | reverses single element | pass |
| 4 | reverses with step -2 | pass |

**Example:** reverses entire array
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr[::-1] == [5, 4, 3, 2, 1]

**Example:** reverses empty array
    Given val arr: [i64] = []
    Then  expect arr[::-1] == []

**Example:** reverses single element
    Given val arr = [42]
    Then  expect arr[::-1] == [42]

**Example:** reverses with step -2
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    Then  expect arr[::-2] == [9, 7, 5, 3, 1]

### Scenario: step on strings

| # | Example | Status |
|---|---------|--------|
| 1 | selects every other character | pass |
| 2 | reverses string | pass |
| 3 | selects odd-indexed characters | pass |
| 4 | slices string with step | pass |

**Example:** selects every other character
    Given val s = "abcdefgh"
    Then  expect s[::2] == "aceg"

**Example:** reverses string
    Given val s = "hello"
    Then  expect s[::-1] == "olleh"

**Example:** selects odd-indexed characters
    Given val s = "abcdefgh"
    Then  expect s[1::2] == "bdfh"

**Example:** slices string with step
    Given val s = "0123456789"
    Then  expect s[1:8:2] == "1357"

### Scenario: edge cases

| # | Example | Status |
|---|---------|--------|
| 1 | handles step equal to length | pass |
| 2 | handles step greater than length | pass |
| 3 | handles step of 1 (identity) | pass |
| 4 | handles empty slice with step | pass |

**Example:** handles step equal to length
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr[::5] == [1]

**Example:** handles step greater than length
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr[::10] == [1]

**Example:** handles step of 1 (identity)
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr[::1] == [1, 2, 3, 4, 5]

**Example:** handles empty slice with step
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr[5:5:2] == []

### Scenario: practical examples

| # | Example | Status |
|---|---------|--------|
| 1 | extracts even indices | pass |
| 2 | extracts odd indices | pass |
| 3 | reverses for iteration | pass |
| 4 | samples at regular intervals | pass |

**Example:** extracts even indices
    Given val data = ["a", "b", "c", "d", "e", "f"]
    Then  expect data[::2] == ["a", "c", "e"]

**Example:** extracts odd indices
    Given val data = ["a", "b", "c", "d", "e", "f"]
    Then  expect data[1::2] == ["b", "d", "f"]

**Example:** reverses for iteration
    Given val nums = [1, 2, 3, 4, 5]
    Given var sum = 0
    Then  expect sum == 54321

**Example:** samples at regular intervals
    Given val readings = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
    Given val sampled = readings[::3]
    Then  expect sampled == [10, 40, 70, 100]


