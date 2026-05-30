# pass unit equivalence
*Source:* `test/feature/usage/pass_unit_equivalence_spec.spl`

## Overview

Pass and Unit Value Equivalence Spec

Category: Control Flow
Status: Implemented

Tests that `pass` and `()` are synonymous in Simple.
- `pass` is a no-op statement (like Python's pass)
- `()` is the unit value
- Both compile to identical code

## Feature: pass and () equivalence

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | both work as standalone statements | pass |
| 2 | both work in if-else branches | pass |
| 3 | both work in loops | pass |

**Example:** both work as standalone statements
    Given var executed = false
    Then  expect executed == true
    Then  expect executed == true

**Example:** both work in if-else branches
    Given val x = 5
    Given var branch_taken = ""
    Then  expect branch_taken == "other"
    Then  expect branch_taken == "other"

**Example:** both work in loops
    Given var count = 0
    Then  expect count == 3
    Then  expect count == 3

## Feature: pass and () documentation

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | documents that pass is no-op statement | pass |

**Example:** documents that pass is no-op statement
    Given var x = 0
    Then  expect x == 1

## Feature: style guidelines

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | recommends pass for explicit no-op intent | pass |

**Example:** recommends pass for explicit no-op intent
    Given var logged = false
    Then  expect logged == false


