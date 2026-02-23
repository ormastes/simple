# Async Features Specification

**Feature ID:** #ASYNC-001 to #ASYNC-063 | **Category:** Runtime | Async | **Status:** Implemented

_Source: `test/feature/usage/async_features_spec.spl`_

---

Tests async features including:
- Lambda expressions
- Future creation and await
- Async functions
- Generators and yield
- Codegen/interpreter parity

Features not supported by runtime parser:
- async fn syntax
- await keyword
- spawn keyword
- yield keyword
- generator() function

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 15 |

## Test Structure

### Lambda Expressions

- ✅ basic lambda with single param
- ✅ lambda with multiple params
- ✅ lambda capturing outer variable
- ✅ immediately invoked lambda
- ✅ nested lambda calls
- ✅ lambda with no params
### Basic Futures

### Async Functions

### Basic Generators

### Await Non-Future Error

- ✅ await requires future type
### Generator State Machine

### Future with Captures

### Actor Spawn

### Generator with State and Capture

### Control Flow Parity

- ✅ nested control flow
- ✅ recursive function
### Data Structure Parity

- ✅ struct field access
- ✅ array operations
- ✅ dictionary access
### Function Parity

- ✅ function composition
- ✅ early return
- ✅ boolean logic

