# Control Flow - If/Else Specification

**Feature ID:** #1001 | **Category:** Language | **Status:** In Progress

_Source: `test/feature/usage/control_flow_if_else_spec.spl`_

---

use std.text.{NL}

Tests for conditional control flow using if/else statements.
Verifies correct evaluation of conditions and execution of appropriate branches.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 11 |

## Test Structure

### Control Flow - If/Else

#### basic if statements

- ✅ executes if body when condition is true
- ✅ skips if body when condition is false
#### if-else statements

- ✅ executes if body when condition is true
- ✅ executes else body when condition is false
#### nested if statements

- ✅ handles nested if statements
- ✅ handles nested if-else
#### if-else-if chains

- ✅ evaluates first matching condition
- ✅ executes final else when no conditions match
#### if with boolean expressions

- ✅ evaluates AND conditions
- ✅ evaluates OR conditions
- ✅ evaluates NOT conditions

