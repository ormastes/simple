# Lambdas and Closures Specification

**Feature ID:** #2300 | **Category:** Language | **Status:** Implemented

_Source: `test/feature/usage/lambdas_closures_spec.spl`_

---

## Key Concepts

| Concept | Description |
|---------|-------------|
| Lambda | Anonymous function defined inline with `\` syntax |
| Closure | Function that captures variables from enclosing scope |
| Higher-Order Function | Function taking or returning other functions |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 13 |

## Test Structure

### Basic Lambdas

- ✅ creates simple lambda
- ✅ creates lambda with multiple params
- ✅ creates lambda with no params
- ✅ invokes lambda immediately
### Closures

- ✅ captures outer variable
- ✅ captures multiple variables
- ✅ nested lambda calls
### Lambdas with Collections

- ✅ maps with lambda
- ✅ filters with lambda
- ✅ reduces with lambda
### Lambda Edge Cases

- ✅ lambda returning lambda
- ✅ lambda as function parameter
- ✅ lambda with conditional

