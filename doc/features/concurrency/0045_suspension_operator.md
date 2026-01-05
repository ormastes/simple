# #45 Suspension Operator (~)

**Status:** 🔄 Planning
**Difficulty:** 3 (Medium)
**Implementation:** Rust
**Spec:** [suspension_operator.md](../../spec/suspension_operator.md)
**Plan:** [async_default_implementation.md](../../plans/async_default_implementation.md)

## Description

The `~` operator marks explicit suspension points for async operations, making async control flow visible at the syntax level.

## Syntax

| Syntax | Context | Meaning |
|--------|---------|---------|
| `x ~= expr` | Assignment | Await and assign |
| `if~ cond:` | Guard | Suspending condition |
| `while~ cond:` | Guard | Suspending loop condition |
| `for~ x in iter:` | Loop | Async iterator |
| `and~`, `or~` | Boolean | Suspending operand |
| `~+=`, `~-=` | Compound | Suspending modify-assign |

## Examples

```simple
# Suspending assignment
let user ~= fetch_user(id)

# Suspending guard
if~ is_ready():
    proceed()

# Suspending loop
while~ not done():
    _ ~= timer.sleep(100_ms)

# Chained conditions
if~ check_auth() and~ has_permission():
    allow()

# Compound assignment
counter ~+= fetch_delta()
```

## Key Features

- **Explicit suspension**: Visible in source code
- **LL(1) compatible**: Unambiguous parsing
- **Composes with `?`**: `let x ~= fetch()?` works
- **Effect enforcement**: `sync fn` cannot use `~`

## Test Locations

- **Simple:** `simple/std_lib/test/features/concurrency/suspension_operator_spec.spl`
- **Rust:** `src/driver/tests/runner_async_tests.rs`

## Related Features

- #44 Async Default
- #46 Effect Inference
- #41 Async/Await
