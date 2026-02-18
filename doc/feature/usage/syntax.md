# Simple Language Syntax Specification - Test Specification
*Source:* `test/feature/usage/syntax_spec.spl`
**Feature IDs:** #10-19  |  **Status:** Stable

## Overview


**Last Updated:** 2026-02-08
**Topics:** syntax, type-system
**Symbols:** Token, Operator, Parser, Lexer
**Module:** simple_parser
**Migrated From:** doc/spec/syntax.md

## Overview

Comprehensive tests for Simple's syntax, including literals, string interpolation,
operators, and indentation-based parsing.

Simple uses Python-like indentation with type annotations and explicit execution mode control.

## Related Specifications

- **Types** - Type annotations and type syntax
- **Functions** - Function definition syntax
- **Parser** - Parser implementation details

## Feature: Syntax Spec

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | syntax overview - if/else | pass |
| 2 | syntax overview - iteration | pass |
| 3 | literals - integer formats | pass |
| 4 | literals - floating point | pass |
| 5 | literals - typed suffixes | pass |
| 6 | string literals - interpolation | pass |
| 7 | string literals - raw strings | pass |
| 8 | string literals - basic interpolation | pass |
| 9 | functional update syntax - arrays | pass |
| 10 | functional update syntax - basic | pass |
| 11 | functional update syntax - lists | pass |
| 12 | functional update syntax - pattern 1 | pass |
| 13 | functional update syntax - pattern 2 | pass |
| 14 | parsing design rationale - simplicity | pass |
| 15 | parsing design rationale - lambdas | pass |

**Example:** syntax overview - if/else
    Given val x = 1

**Example:** syntax overview - iteration
    Given val list = [1, 2, 3]

**Example:** literals - integer formats
    Given val count = 1_000_000
    Given val color = 0xFF5733
    Given val mask = 0x0000_FFFF
    Given val flags = 0b1010_0101
    Given val permissions = 0o755

**Example:** literals - floating point
    Given val pi = 3.14159

**Example:** string literals - interpolation
    Given val name = "world"
    Given val count = 42
    Given val msg = "Hello, {name}! Count is {count + 1}"

**Example:** string literals - raw strings
    Given val regex = '[a-z]+\d{2,3}'
    Given val path = 'C:\Users{NL}ame'

**Example:** string literals - basic interpolation
    Given val name = "world"
    Given val msg = "Hello, {name}!"

**Example:** functional update syntax - arrays
    Given var data = [1, 2, 3]

**Example:** functional update syntax - lists
    Given var list = [1, 2, 3]

**Example:** parsing design rationale - lambdas
    Given val double = \x: x * 2


