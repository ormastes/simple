# Stackless Coroutines Specification

**Feature ID:** #STACKLESS-CORO | **Category:** Runtime | **Status:** Implemented

_Source: `test/feature/usage/stackless_coroutines_spec.spl`_

---

Stackless coroutines provide lightweight concurrency without allocating stack
space for each coroutine. They support async/await syntax, yield operations,
and generator functions.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 20 |

## Test Structure

### Generator Functions

#### simple generators

- ✅ creates generator that yields values
- ✅ generator evaluates lazily
#### generator state

- ✅ preserves state across iterations
- ✅ generator with multiple yields
### Async/Await

#### basic async functions

- ✅ defines async function
- ✅ handles async computation
#### error handling in async

- ✅ chains async operations
#### async resource management

### Yield Operations

#### basic yield

- ✅ yields single value
- ✅ yields multiple values
#### yield with computed values

- ✅ yields computed expressions
- ✅ yields based on conditions
### Coroutine Scheduling

#### multiple coroutines

- ✅ runs multiple generators
#### efficient scheduling

- ✅ avoids stack allocation overhead
- ✅ handles many coroutines
### Coroutine Lifecycle

#### coroutine creation

- ✅ creates coroutine in initial state
#### coroutine completion

- ✅ completes after yielding all values
- ✅ cleanup happens on completion
#### coroutine state transitions

- ✅ transitions from created to running
- ✅ transitions through suspend and resume
- ✅ transitions to completed

