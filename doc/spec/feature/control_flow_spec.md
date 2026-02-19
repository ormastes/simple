# Control Flow Module

**Feature ID:** #RUNTIME-001 | **Category:** Runtime | **Status:** Active

_Source: `test/feature/interpreter/control_flow_spec.spl`_

---

## Overview

Tests the interpreter control flow module implementations covering for loops (eval_for), while
loops (eval_while), infinite loops (eval_loop), if/else conditionals (eval_if), and pattern
matching (eval_match). Validates iterable evaluation, loop variable scoping, break/continue
signals, condition checking, tuple and array pattern binding with wildcard fallback, and
integration tests combining nested control flow constructs.

## Syntax

```simple
var sum = 0
for i in 1..5:
    sum = sum + i
expect sum == 10

val result = match (1, 2):
    case (1, x): x * 10
    case _: 0
expect result == 20
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 24 |

## Test Structure

### eval_for

#### iterable evaluation

- ✅ evaluates iterable before loop
- ✅ evaluates range expression
#### loop variable scope

- ✅ creates new scope for loop variable
- ✅ binds loop variable for each iteration
#### control flow signals

- ✅ handles break with value
- ✅ handles continue signal
### eval_while

#### condition evaluation

- ✅ checks condition before each iteration
- ✅ does not execute body if condition is false
#### control flow signals

- ✅ handles continue signal
- ✅ handles break signal
### eval_loop

#### break signal

- ✅ breaks on Break signal
- ✅ can break with computed condition
### eval_if

#### condition evaluation

- ✅ evaluates true condition
- ✅ evaluates false condition
- ✅ evaluates comparison expression
#### branch execution

- ✅ executes then branch when true
- ✅ executes else branch when false
### eval_match

#### tuple matching

- ✅ matches tuple and binds variables
- ✅ uses wildcard for unmatched patterns
#### array matching

- ✅ matches array and binds elements
- ✅ handles array length mismatch
### Control Flow Integration

- ✅ nests for inside while
- ✅ nests if inside for
- ✅ combines match with for

