# Future Body Execution and Deferred Evaluation

**Feature ID:** #RT-021 | **Category:** Runtime | **Status:** In Progress

_Source: `test/feature/usage/future_body_execution_spec.spl`_

---

## Overview

Futures in Simple wrap deferred computations created with `future(expr)` and forced
with `await`. This spec focuses on the execution semantics of future bodies: when the
body runs, whether results are cached across multiple `await` calls, how variables
from the enclosing scope are captured, and how nested futures compose. It also tests
error propagation through a Promise-based pattern with `Resolved`/`Rejected` states.
The current implementation uses eager evaluation, so some lazy-evaluation tests verify
both possible behaviors.

## Syntax

```simple
val f = future(10 + 32)
val result = await f                # forces evaluation, returns 42

val x = 10
val y = 20
val f2 = future(x + y)             # captures variables from scope
expect await f2 == 30

val f1 = future(10)
val f2 = future(await f1 * 2)      # nested future composition
expect await f2 == 20
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `future(expr)` | Creates a deferred computation wrapping the given expression |
| `await` | Forces a future to execute its body and returns the result |
| Result caching | Awaiting the same future multiple times returns the same cached result |
| Variable capture | Futures capture variables from their defining scope at creation time |
| Nested futures | A future body can `await` other futures, enabling composition |
| Promise states | `Pending`, `Resolved(value)`, and `Rejected(error)` for async error handling |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 11 |

## Test Structure

### Future Body Execution

#### when a future body is created

- ✅ delays execution until forced
- ✅ executes body only once
#### when a future is forced

- ✅ executes the body and returns result
- ✅ caches result for subsequent forces
### Future Body Execution Context

#### when future captures variables

- ✅ captures immutable variables by value
- ✅ captures mutable references correctly
#### when future body has side effects

- ✅ executes side effects when forced
- ✅ side effects do not execute until forced
### Future Body Execution Errors

- ✅ propagates exceptions from body execution
- ✅ handles recursive future execution
- ✅ manages execution in concurrent context

