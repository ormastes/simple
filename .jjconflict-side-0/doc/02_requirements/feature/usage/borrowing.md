# borrowing
*Source:* `test/feature/usage/borrowing_spec.spl`
**Category:** Memory Management  |  **Status:** In Progress

## Overview

Reference Capabilities and Borrowing Specification


Tests for the borrowing system including mutable (mut T), isolated (iso T),
and immutable reference capabilities. Verifies proper ownership transfer,
mutable access restrictions, and isolation guarantees.

## Feature: Borrowing and Reference Capabilities

Tests for the borrowing system that manages memory safety through
    reference capabilities. Verifies that mut T, iso T, and immutable
    references behave correctly and prevent invalid memory access patterns.

### Scenario: Immutable references

| # | Example | Status |
|---|---------|--------|
| 1 | allows multiple immutable borrows | pass |

### Scenario: Mutable references

| # | Example | Status |
|---|---------|--------|
| 1 | prevents simultaneous immutable and mutable borrows | pass |

### Scenario: Isolated references

| # | Example | Status |
|---|---------|--------|
| 1 | ensures exclusive access to isolated values | pass |

### Scenario: Ownership transfer

| # | Example | Status |
|---|---------|--------|
| 1 | transfers ownership correctly through function calls | pass |


