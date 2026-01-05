# #44 Async Default

**Status:** 🔄 Planning
**Difficulty:** 3 (Medium)
**Implementation:** Rust
**Spec:** [async_default.md](../../spec/async_default.md)
**Plan:** [async_default_implementation.md](../../plans/async_default_implementation.md)

## Description

Functions are async by default in Simple. The `sync` keyword explicitly marks non-suspending functions.

## Syntax

```simple
# Async by default (may suspend)
fn fetch_user(id: UserId) -> User:
    let resp ~= http.get("/users/{id}")
    return parse(resp)

# Explicit sync (compiler verifies no suspension)
sync fn compute(x: i64) -> i64:
    return x * x
```

## Key Features

- **Async-by-default**: `fn` may contain suspension operators
- **Explicit sync**: `sync fn` guarantees no suspension
- **Promise wrapping**: Async functions return `Promise[T]` implicitly
- **Effect inference**: Compiler infers async/sync from function body

## Return Type Behavior

| Declaration | Body | Declared Return | Actual Return |
|-------------|------|-----------------|---------------|
| `fn` | Has `~=` | `T` | `Promise[T]` |
| `fn` | No `~=` | `T` | `T` (sync inferred) |
| `sync fn` | Any | `T` | `T` (verified) |

## Test Locations

- **Simple:** `simple/std_lib/test/features/concurrency/async_default_spec.spl`
- **Rust:** `src/driver/tests/runner_async_tests.rs`
- **Lean:** `verification/type_inference_compile/src/AsyncEffectInference.lean`

## Related Features

- #45 Suspension Operator (~)
- #46 Effect Inference
- #47 Promise Type
- #41 Async/Await
