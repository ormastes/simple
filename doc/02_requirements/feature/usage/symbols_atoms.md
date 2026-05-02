# Symbols and Atoms Specification
*Source:* `test/feature/usage/symbols_atoms_spec.spl`
**Feature IDs:** #SYMBOLS-001  |  **Category:** Language | Types  |  **Status:** Implemented

## Overview



## Overview

Symbols (also called atoms) are immutable, interned identifiers that are
compared by identity rather than value. They provide efficient comparison
operations and are commonly used for keys, tags, and enum-like values.

## Syntax

```simple
val status = :ok
val error = :not_found

if status is :ok:
    handle_success()
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Symbol | Interned identifier compared by identity |
| Atom | Alternative name for symbol (Erlang terminology) |
| Interning | Process of storing unique string once |
| Symbol Table | Runtime storage for interned symbols |

## Behavior

- Symbols are prefixed with colon: `:name`
- Symbol comparison is O(1) pointer equality
- All occurrences of same symbol share memory
- Symbols are immutable and cannot be modified

## Feature: Symbol Creation

## Creating Symbols

    Tests for symbol creation using colon prefix syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates simple symbol | pass |
| 2 | creates symbol with underscore | pass |
| 3 | creates multiple distinct symbols | pass |

**Example:** creates simple symbol
    Given val status = :ok
    Given var result = 0
    Then  expect result == 1

**Example:** creates symbol with underscore
    Given val err = :not_found
    Given var result = 0
    Then  expect result == 1

**Example:** creates multiple distinct symbols
    Given val a = :hello
    Given val b = :world
    Given var result = 0
    Then  expect result == 1

## Feature: Symbol Comparison

## Comparing Symbols

    Tests for symbol comparison by identity.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | compares equal symbols | pass |
| 2 | distinguishes different symbols | pass |
| 3 | compares symbol in if-else | pass |
| 4 | compares symbol with not equal | pass |

**Example:** compares equal symbols
    Given val a = :hello
    Given val b = :hello
    Given var result = 0
    Then  expect result == 10

**Example:** distinguishes different symbols
    Given val a = :hello
    Given val b = :world
    Given var result = 1
    Then  expect result == 1

**Example:** compares symbol in if-else
    Given val status = :ok
    Given val result = if status is :ok: 42 else: 0
    Then  expect result == 42

**Example:** compares symbol with not equal
    Given val a = :hello
    Given val b = :world
    Given var result = 0
    Then  expect result == 1

## Feature: Symbol Use Cases

## Practical Symbol Usage

    Tests for common symbol usage patterns.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses symbol as return value | pass |
| 2 | uses symbol as function parameter | pass |
| 3 | uses symbol in conditional logic | pass |
| 4 | chains symbol checks | pass |

**Example:** uses symbol as return value
    Given val result = get_status()
    Given var r = 0
    Then  expect r == 1

**Example:** uses symbol as function parameter
    Then  expect process(:ok) == 42

**Example:** uses symbol in conditional logic
    Given val state = :running
    Given var code = 0
    Then  expect code == 2

**Example:** chains symbol checks
    Given val a = :first
    Given val b = :second
    Given var result = 0
    Then  expect result == 100


